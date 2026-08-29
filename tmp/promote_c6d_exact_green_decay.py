#!/usr/bin/env python3
"""Fail-closed promotion of the exact positive/zero-depth C6d Green decay.

This promotes only the two D2 source/audit pairs.  It never runs Lean and
never removes PRE-VALIDATION.  The D1 precision-localization and named metric
prefix must already be sealed in the selected source commit.
"""

from __future__ import annotations

import argparse
import hashlib
from pathlib import Path
import re
import subprocess


ROOT = Path(__file__).resolve().parents[1]
CORE = "YangMillsCore.lean"
SOURCES = (
    "tmp/BalabanCMP99Eq360C6dSourceSeparatedAmbientGreenDecay.draft.lean",
    "tmp/BalabanCMP99Eq360C6dSourceSeparatedAmbientGreenDecayAudit.draft.lean",
    "tmp/BalabanCMP99Eq360C6dSourceSeparatedAmbientGreenDecayZeroDepth.draft.lean",
    "tmp/BalabanCMP99Eq360C6dSourceSeparatedAmbientGreenDecayZeroDepthAudit.draft.lean",
)
PREREQUISITES = (
    "YangMills/RG/BalabanCMP99Eq360C6dSourceSeparatedAmbientGreen.lean",
    "YangMills/RG/BalabanCMP99Eq360C6dSourceSeparatedAmbientGreenAudit.lean",
    "YangMills/RG/BalabanCMP99Eq360C6dSourceSeparatedAmbientGreenZeroDepth.lean",
    "YangMills/RG/BalabanCMP99Eq360C6dSourceSeparatedAmbientGreenZeroDepthAudit.lean",
    "YangMills/RG/BalabanCMP99SourceActiveRegionFullCompanionPrecisionDecay.lean",
    "YangMills/RG/BalabanCMP99SourceActiveRegionFullCompanionPrecisionDecayAudit.lean",
    "YangMills/RG/BalabanCMP99Eq360C6dSourceSeparatedAmbientMetric.lean",
    "YangMills/RG/BalabanCMP99Eq360C6dSourceSeparatedAmbientMetricAudit.lean",
)


def git(*args: str) -> subprocess.CompletedProcess[bytes]:
    return subprocess.run(
        ["git", "-c", "safe.directory=*", *args],
        cwd=ROOT,
        check=False,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )


def blob(source_sha: str, relative: str) -> bytes:
    child = git("cat-file", "blob", f"{source_sha}:{relative}")
    if child.returncode != 0:
        raise RuntimeError(
            f"C6D_EXACT_GREEN_DECAY_BLOB_FAILED={relative}:"
            + child.stderr.decode(errors="replace")
        )
    return child.stdout


def destination(relative: str) -> str:
    name = Path(relative).name.removesuffix(".draft.lean")
    return f"YangMills/RG/{name}.lean"


def promote_text(data: bytes) -> bytes:
    text = data.decode("utf-8")
    if text.count("SCRATCH ONLY:") != 1:
        raise RuntimeError("C6D_EXACT_GREEN_DECAY_SCRATCH_MARKER_COUNT")
    standard = (
        "PRE-VALIDATION: source present; its `.olean` is not yet materialized "
        "and the result is not compiler-verified."
    )
    markers = (
        "SCRATCH ONLY: this file is neither imported nor compiler-verified and is not\n"
        "evidence.  It may be promoted only after the Green, terminal-block diameter,\n"
        "full-companion precision-decay and metric prefixes have independent verdicts.",
        "SCRATCH ONLY: this file is neither imported nor compiler-verified and is not\n"
        "evidence.  It is the depth-zero companion of the positive-depth D2 draft.",
        "-- SCRATCH ONLY: no compiler or axiom-oracle verdict is claimed.",
    )
    matches = [marker for marker in markers if marker in text]
    if len(matches) != 1:
        raise RuntimeError("C6D_EXACT_GREEN_DECAY_SCRATCH_PROSE_UNRECOGNIZED")
    replacement = standard if not matches[0].startswith("-- ") else "-- " + standard
    text = text.replace(matches[0], replacement, 1)
    text = re.sub(
        r"^import tmp\.([A-Za-z0-9_]+)\.draft$",
        r"import YangMills.RG.\1",
        text,
        flags=re.MULTILINE,
    )
    if "import tmp." in text:
        raise RuntimeError("C6D_EXACT_GREEN_DECAY_TMP_IMPORT_REMAINS")
    if text.count("PRE-VALIDATION:") != 1:
        raise RuntimeError("C6D_EXACT_GREEN_DECAY_PRE_COUNT")
    if re.search(r"(?m)^\s*axiom\b|\b(?:sorry|admit|by\?|exact\?)\b", text):
        raise RuntimeError("C6D_EXACT_GREEN_DECAY_PLACEHOLDER")
    return text.encode("utf-8")


def require_clean_blob(source_sha: str, relative: str) -> bytes:
    status = git("status", "--porcelain=v1", "--", relative)
    if status.returncode != 0 or status.stdout:
        raise RuntimeError(f"C6D_EXACT_GREEN_DECAY_DIRTY={relative}")
    data = blob(source_sha, relative)
    if (ROOT / relative).read_bytes().replace(b"\r\n", b"\n") != data:
        raise RuntimeError(f"C6D_EXACT_GREEN_DECAY_DIVERGED={relative}")
    return data


def digest(rows: list[tuple[str, bytes]]) -> str:
    payload = b"".join(
        f"{hashlib.sha256(data).hexdigest().upper()}  {relative}\n".encode()
        for relative, data in rows
    )
    return hashlib.sha256(payload).hexdigest().upper()


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--source-sha", required=True)
    parser.add_argument("--apply", action="store_true")
    args = parser.parse_args()
    if re.fullmatch(r"[0-9a-f]{40}", args.source_sha) is None:
        raise RuntimeError("C6D_EXACT_GREEN_DECAY_SOURCE_SHA_INVALID")
    resolved = git("rev-parse", f"{args.source_sha}^{{commit}}")
    if resolved.returncode != 0 or resolved.stdout.decode().strip() != args.source_sha:
        raise RuntimeError("C6D_EXACT_GREEN_DECAY_SOURCE_COMMIT_MISMATCH")

    for relative in PREREQUISITES:
        if b"PRE-VALIDATION:" in blob(args.source_sha, relative):
            raise RuntimeError(f"C6D_EXACT_GREEN_DECAY_PREREQ_UNSEALED={relative}")

    rows: list[tuple[str, bytes]] = []
    for relative in SOURCES:
        target = destination(relative)
        if git("cat-file", "-e", f"{args.source_sha}:{target}").returncode == 0:
            raise RuntimeError(f"C6D_EXACT_GREEN_DECAY_TARGET_EXISTS={target}")
        if (ROOT / target).exists() or git(
            "status", "--porcelain=v1", "--", target
        ).stdout:
            raise RuntimeError(f"C6D_EXACT_GREEN_DECAY_TARGET_DIRTY={target}")
        rows.append((target, promote_text(require_clean_blob(args.source_sha, relative))))

    core_status = git("status", "--porcelain=v1", "--", CORE)
    if core_status.returncode != 0 or core_status.stdout:
        raise RuntimeError("C6D_EXACT_GREEN_DECAY_CORE_DIRTY")
    core = blob(args.source_sha, CORE).decode("utf-8")
    imports = (
        "import YangMills.RG.BalabanCMP99Eq360C6dSourceSeparatedAmbientGreenDecayAudit",
        "import YangMills.RG.BalabanCMP99Eq360C6dSourceSeparatedAmbientGreenDecayZeroDepthAudit",
    )
    for line in imports:
        if line in core:
            raise RuntimeError(f"C6D_EXACT_GREEN_DECAY_CORE_IMPORT_EXISTS={line}")
    if not core.endswith("\n"):
        core += "\n"
    rows.append((CORE, (core + "\n".join(imports) + "\n").encode("utf-8")))

    manifest = digest(rows)
    if not args.apply:
        print(
            "C6D_EXACT_GREEN_DECAY_PROMOTION_PREVIEW_OK "
            f"files={len(rows)} promoted={len(SOURCES)} "
            f"source_sha={args.source_sha} manifest_sha256={manifest}"
        )
        return 0

    originals = {
        relative: (ROOT / relative).read_bytes() if (ROOT / relative).exists() else None
        for relative, _ in rows
    }
    written: list[str] = []
    try:
        for relative, data in rows:
            target = ROOT / relative
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes(data)
            written.append(relative)
        actual = digest(
            [(relative, (ROOT / relative).read_bytes()) for relative, _ in rows]
        )
        if actual != manifest:
            raise RuntimeError(
                f"C6D_EXACT_GREEN_DECAY_POSTWRITE={actual} EXPECTED={manifest}"
            )
    except Exception:
        for relative in reversed(written):
            original = originals[relative]
            if original is None:
                (ROOT / relative).unlink(missing_ok=True)
            else:
                (ROOT / relative).write_bytes(original)
        raise

    print(
        "C6D_EXACT_GREEN_DECAY_PROMOTION_APPLY_OK "
        f"files={len(rows)} promoted={len(SOURCES)} "
        f"source_sha={args.source_sha} manifest_sha256={manifest}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
