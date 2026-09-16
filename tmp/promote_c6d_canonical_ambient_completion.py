#!/usr/bin/env python3
"""Fail-closed promotion of the canonical regional ambient completion pair."""

from __future__ import annotations

import argparse
import hashlib
from pathlib import Path
import re
import subprocess


ROOT = Path(__file__).resolve().parents[1]
CORE = "YangMillsCore.lean"
SOURCES = (
    "tmp/BalabanCMP99ActiveRegionCanonicalAmbientCompletion.draft.lean",
    "tmp/BalabanCMP99ActiveRegionCanonicalAmbientCompletionAudit.draft.lean",
)
PREREQUISITES = (
    "YangMills/RG/BalabanCMP99LocalizedParametrix.lean",
    "YangMills/RG/BalabanCMP99SourceRegionalGreenNeumann.lean",
    "YangMills/RG/BalabanCMP99SourceEq395LocalInverse.lean",
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
            f"C6D_CANONICAL_COMPLETION_BLOB_FAILED={relative}:"
            + child.stderr.decode(errors="replace")
        )
    return child.stdout


def destination(relative: str) -> str:
    name = Path(relative).name.removesuffix(".draft.lean")
    return f"YangMills/RG/{name}.lean"


def retarget(data: bytes) -> bytes:
    text = re.sub(
        r"^import tmp\.([A-Za-z0-9_]+)\.draft$",
        r"import YangMills.RG.\1",
        data.decode("utf-8"),
        flags=re.MULTILINE,
    )
    if "import tmp." in text:
        raise RuntimeError("C6D_CANONICAL_COMPLETION_TMP_IMPORT_REMAINS")
    if text.count("PRE-VALIDATION:") != 1:
        raise RuntimeError("C6D_CANONICAL_COMPLETION_PRE_COUNT")
    if re.search(r"(?m)^\s*axiom\b|\b(?:sorry|admit|by\?|exact\?)\b", text):
        raise RuntimeError("C6D_CANONICAL_COMPLETION_PLACEHOLDER")
    return text.encode("utf-8")


def require_clean(source_sha: str, relative: str) -> bytes:
    status = git("status", "--porcelain=v1", "--", relative)
    if status.returncode != 0 or status.stdout:
        raise RuntimeError(f"C6D_CANONICAL_COMPLETION_DIRTY={relative}")
    data = blob(source_sha, relative)
    if (ROOT / relative).read_bytes().replace(b"\r\n", b"\n") != data:
        raise RuntimeError(f"C6D_CANONICAL_COMPLETION_DIVERGED={relative}")
    return data


def manifest_digest(rows: list[tuple[str, bytes]]) -> str:
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
        raise RuntimeError("C6D_CANONICAL_COMPLETION_SOURCE_SHA_INVALID")
    resolved = git("rev-parse", f"{args.source_sha}^{{commit}}")
    if resolved.returncode != 0 or resolved.stdout.decode().strip() != args.source_sha:
        raise RuntimeError("C6D_CANONICAL_COMPLETION_SOURCE_COMMIT_MISMATCH")
    for relative in PREREQUISITES:
        if b"PRE-VALIDATION:" in blob(args.source_sha, relative):
            raise RuntimeError(f"C6D_CANONICAL_COMPLETION_PREREQ_UNSEALED={relative}")

    rows: list[tuple[str, bytes]] = []
    for relative in SOURCES:
        target = destination(relative)
        if git("cat-file", "-e", f"{args.source_sha}:{target}").returncode == 0:
            raise RuntimeError(f"C6D_CANONICAL_COMPLETION_TARGET_EXISTS={target}")
        if (ROOT / target).exists() or git("status", "--porcelain=v1", "--", target).stdout:
            raise RuntimeError(f"C6D_CANONICAL_COMPLETION_TARGET_DIRTY={target}")
        rows.append((target, retarget(require_clean(args.source_sha, relative))))

    core_status = git("status", "--porcelain=v1", "--", CORE)
    if core_status.returncode != 0 or core_status.stdout:
        raise RuntimeError("C6D_CANONICAL_COMPLETION_CORE_DIRTY")
    core = blob(args.source_sha, CORE).decode("utf-8")
    audit_import = (
        "import YangMills.RG."
        "BalabanCMP99ActiveRegionCanonicalAmbientCompletionAudit"
    )
    if audit_import in core:
        raise RuntimeError("C6D_CANONICAL_COMPLETION_CORE_IMPORT_EXISTS")
    if not core.endswith("\n"):
        core += "\n"
    rows.append((CORE, (core + audit_import + "\n").encode("utf-8")))
    digest = manifest_digest(rows)
    if not args.apply:
        print(
            "C6D_CANONICAL_AMBIENT_COMPLETION_PROMOTION_PREVIEW_OK "
            f"files=3 promoted=2 source_sha={args.source_sha} "
            f"manifest_sha256={digest}"
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
        actual = manifest_digest(
            [(relative, (ROOT / relative).read_bytes()) for relative, _ in rows]
        )
        if actual != digest:
            raise RuntimeError(
                f"C6D_CANONICAL_COMPLETION_POSTWRITE={actual} EXPECTED={digest}"
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
        "C6D_CANONICAL_AMBIENT_COMPLETION_PROMOTION_APPLY_OK "
        f"files=3 promoted=2 source_sha={args.source_sha} "
        f"manifest_sha256={digest}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
