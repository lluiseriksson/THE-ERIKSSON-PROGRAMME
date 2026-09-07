#!/usr/bin/env python3
"""Fail-closed promotion of the exact C6d Green value-action prefix.

This script performs text transport only.  It never runs Lean and never
removes PRE-VALIDATION.  The exact D2 positive- and zero-depth pairs and the
physical source-background dictionary must be sealed first.
"""

from __future__ import annotations

import argparse
import hashlib
from pathlib import Path
import re
import subprocess


ROOT = Path(__file__).resolve().parents[1]
CORE = "YangMillsCore.lean"
MANIFEST = ROOT / "tmp" / "c6d-exact-green-value-prefix-draft-paths.txt"
PREREQUISITES = (
    "YangMills/RG/BalabanCMP99Eq360C6dSourceSeparatedAmbientGreenDecay.lean",
    "YangMills/RG/BalabanCMP99Eq360C6dSourceSeparatedAmbientGreenDecayAudit.lean",
    "YangMills/RG/BalabanCMP99Eq360C6dSourceSeparatedAmbientGreenDecayZeroDepth.lean",
    "YangMills/RG/BalabanCMP99Eq360C6dSourceSeparatedAmbientGreenDecayZeroDepthAudit.lean",
    "YangMills/RG/BalabanCMP99Eq360C6dSourceSeparatedPhysicalBackground.lean",
    "YangMills/RG/BalabanCMP99Eq360C6dSourceSeparatedPhysicalBackgroundAudit.lean",
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
            f"C6D_VALUE_PREFIX_BLOB_FAILED={relative}:"
            + child.stderr.decode(errors="replace")
        )
    return child.stdout


def source_paths() -> tuple[str, ...]:
    rows = tuple(
        line.strip()
        for line in MANIFEST.read_text(encoding="utf-8").splitlines()
        if line.strip() and not line.lstrip().startswith("#")
    )
    if len(rows) != 12 or len(set(rows)) != len(rows):
        raise RuntimeError(f"C6D_VALUE_PREFIX_MANIFEST_COUNT={len(rows)} EXPECTED=12")
    return rows


def destination(relative: str) -> str:
    name = Path(relative).name.removesuffix(".draft.lean")
    return f"YangMills/RG/{name}.lean"


def promote_text(data: bytes) -> bytes:
    text = data.decode("utf-8")
    standard = (
        "PRE-VALIDATION: source present; its `.olean` is not yet materialized "
        "and the result is not compiler-verified."
    )
    prose = (
        "SCRATCH ONLY: this file is neither imported nor compiler-verified and is not\n"
        "evidence."
    )
    line = "SCRATCH ONLY: no compiler or axiom-oracle verdict is claimed."
    count = text.count(prose) + text.count(line)
    if count != 1:
        raise RuntimeError(f"C6D_VALUE_PREFIX_SCRATCH_MARKER_COUNT={count}")
    if prose in text:
        text = text.replace(prose, standard, 1)
    else:
        text = text.replace(line, standard, 1)
    if text.count("PRE-VALIDATION:") != 1:
        raise RuntimeError("C6D_VALUE_PREFIX_PRE_COUNT")
    if "SCRATCH ONLY:" in text:
        raise RuntimeError("C6D_VALUE_PREFIX_SCRATCH_REMAINS")
    if re.search(r"(?m)^\s*axiom\b|\b(?:sorry|admit|by\?|exact\?)\b", text):
        raise RuntimeError("C6D_VALUE_PREFIX_PLACEHOLDER")
    return text.encode("utf-8")


def require_clean_blob(source_sha: str, relative: str) -> bytes:
    status = git("status", "--porcelain=v1", "--", relative)
    if status.returncode != 0 or status.stdout:
        raise RuntimeError(f"C6D_VALUE_PREFIX_DIRTY={relative}")
    data = blob(source_sha, relative)
    if (ROOT / relative).read_bytes().replace(b"\r\n", b"\n") != data:
        raise RuntimeError(f"C6D_VALUE_PREFIX_DIVERGED={relative}")
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
        raise RuntimeError("C6D_VALUE_PREFIX_SOURCE_SHA_INVALID")
    resolved = git("rev-parse", f"{args.source_sha}^{{commit}}")
    if resolved.returncode != 0 or resolved.stdout.decode().strip() != args.source_sha:
        raise RuntimeError("C6D_VALUE_PREFIX_SOURCE_COMMIT_MISMATCH")

    for relative in PREREQUISITES:
        data = blob(args.source_sha, relative)
        if b"PRE-VALIDATION:" in data:
            raise RuntimeError(f"C6D_VALUE_PREFIX_PREREQ_UNSEALED={relative}")

    sources = source_paths()
    rows: list[tuple[str, bytes]] = []
    for relative in sources:
        target = destination(relative)
        if git("cat-file", "-e", f"{args.source_sha}:{target}").returncode == 0:
            raise RuntimeError(f"C6D_VALUE_PREFIX_TARGET_EXISTS={target}")
        if (ROOT / target).exists() or git(
            "status", "--porcelain=v1", "--", target
        ).stdout:
            raise RuntimeError(f"C6D_VALUE_PREFIX_TARGET_DIRTY={target}")
        rows.append((target, promote_text(require_clean_blob(args.source_sha, relative))))

    core_status = git("status", "--porcelain=v1", "--", CORE)
    if core_status.returncode != 0 or core_status.stdout:
        raise RuntimeError("C6D_VALUE_PREFIX_CORE_DIRTY")
    core = blob(args.source_sha, CORE).decode("utf-8")
    audit_imports = tuple(
        "import YangMills.RG." + Path(relative).name.removesuffix(".draft.lean")
        for relative in sources
        if relative.endswith("Audit.draft.lean")
    )
    if len(audit_imports) != 6:
        raise RuntimeError("C6D_VALUE_PREFIX_AUDIT_IMPORT_COUNT")
    for line in audit_imports:
        if line in core:
            raise RuntimeError(f"C6D_VALUE_PREFIX_CORE_IMPORT_EXISTS={line}")
    if not core.endswith("\n"):
        core += "\n"
    rows.append((CORE, (core + "\n".join(audit_imports) + "\n").encode("utf-8")))

    manifest = digest(rows)
    if not args.apply:
        print(
            "C6D_VALUE_PREFIX_PROMOTION_PREVIEW_OK "
            f"files={len(rows)} promoted={len(sources)} "
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
                f"C6D_VALUE_PREFIX_POSTWRITE={actual} EXPECTED={manifest}"
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
        "C6D_VALUE_PREFIX_PROMOTION_APPLY_OK "
        f"files={len(rows)} promoted={len(sources)} "
        f"source_sha={args.source_sha} manifest_sha256={manifest}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
