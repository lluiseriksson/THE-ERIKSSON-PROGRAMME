#!/usr/bin/env python3
"""Fail-closed PRE-VALIDATION promotion of the closed Eq. (3.37) recursion."""

from __future__ import annotations

import argparse
import hashlib
from pathlib import Path
import re
import subprocess


ROOT = Path(__file__).resolve().parents[1]
PATHS_FILE = ROOT / "tmp" / "EQ337-CLOSED-PHYSICAL-RECURSION-DRAFT-PATHS.txt"
CORE = "YangMillsCore.lean"
REQUIRED_PREREQUISITES = (
    "YangMills/RG/BalabanCMP99Eq337PhysicalComplexUbarDeviationRadius.lean",
    "YangMills/RG/BalabanCMP99ComplexUbarSmallFieldPropagation.lean",
)


def git(*args: str) -> subprocess.CompletedProcess[bytes]:
    return subprocess.run(
        ["git", "-c", "safe.directory=*", *args],
        cwd=ROOT,
        check=False,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )


def require_commit(source_sha: str) -> None:
    if re.fullmatch(r"[0-9a-f]{40}", source_sha) is None:
        raise RuntimeError("EQ337_CLOSED_PHYSICAL_SOURCE_SHA_INVALID")
    child = git("rev-parse", f"{source_sha}^{{commit}}")
    if child.returncode != 0 or child.stdout.decode().strip() != source_sha:
        raise RuntimeError("EQ337_CLOSED_PHYSICAL_SOURCE_COMMIT_MISMATCH")


def git_blob(source_sha: str, relative: str) -> bytes:
    child = git("cat-file", "blob", f"{source_sha}:{relative}")
    if child.returncode != 0:
        raise RuntimeError(
            f"EQ337_CLOSED_PHYSICAL_BLOB_FAILED={relative}:"
            + child.stderr.decode(errors="replace")
        )
    return child.stdout


def paths() -> list[str]:
    rows = [
        line.strip()
        for line in PATHS_FILE.read_text(encoding="utf-8").splitlines()
        if line.strip()
    ]
    if len(rows) != 6 or len(set(rows)) != 6:
        raise RuntimeError(
            f"EQ337_CLOSED_PHYSICAL_SCOPE={len(rows)}/{len(set(rows))} WANT=6/6"
        )
    return rows


def destination(relative: str) -> str:
    path = Path(relative)
    if path.parent.as_posix() != "tmp" or not path.name.endswith(".draft.lean"):
        raise RuntimeError(f"EQ337_CLOSED_PHYSICAL_PATH_INVALID={relative}")
    return f"YangMills/RG/{path.name.removesuffix('.draft.lean')}.lean"


def require_clean_blob(source_sha: str, relative: str) -> bytes:
    status = git("status", "--porcelain=v1", "--", relative)
    if status.returncode != 0 or status.stdout:
        raise RuntimeError(
            f"EQ337_CLOSED_PHYSICAL_DIRTY={relative}:"
            + status.stdout.decode(errors="replace").strip()
        )
    data = git_blob(source_sha, relative)
    worktree = (ROOT / relative).read_bytes().replace(b"\r\n", b"\n")
    if worktree != data:
        raise RuntimeError(f"EQ337_CLOSED_PHYSICAL_WORKTREE_DIVERGED={relative}")
    return data


def require_absent(source_sha: str, relative: str) -> None:
    status = git("status", "--porcelain=v1", "--", relative)
    if status.returncode != 0 or status.stdout:
        raise RuntimeError(f"EQ337_CLOSED_PHYSICAL_DESTINATION_DIRTY={relative}")
    probe = git("cat-file", "-e", f"{source_sha}:{relative}")
    if probe.returncode == 0 or (ROOT / relative).exists():
        raise RuntimeError(f"EQ337_CLOSED_PHYSICAL_DESTINATION_EXISTS={relative}")


def retarget_imports(data: bytes) -> bytes:
    text = data.decode("utf-8")
    text = re.sub(
        r"^import tmp\.([A-Za-z0-9_]+)\.draft$",
        r"import YangMills.RG.\1",
        text,
        flags=re.MULTILINE,
    )
    if "import tmp." in text:
        raise RuntimeError("EQ337_CLOSED_PHYSICAL_TMP_IMPORT_REMAINS")
    if text.count("PRE-VALIDATION:") != 1:
        raise RuntimeError("EQ337_CLOSED_PHYSICAL_PREVALIDATION_COUNT_MISMATCH")
    return text.encode("utf-8")


def require_prerequisites(source_sha: str) -> None:
    for relative in REQUIRED_PREREQUISITES:
        data = git_blob(source_sha, relative)
        if b"PRE-VALIDATION:" in data:
            raise RuntimeError(f"EQ337_CLOSED_PHYSICAL_PREREQUISITE_UNSEALED={relative}")


def core_with_audits(data: bytes) -> bytes:
    imports = (
        "import YangMills.RG.BalabanCMP99Eq337ComplexClosedRadiusPhysicalBridgeAudit",
        "import YangMills.RG.BalabanCMP99Eq337ComplexClosedRadiusPhysicalGatesAudit",
        "import YangMills.RG.BalabanCMP99Eq337ComplexClosedRecursiveBackgroundAudit",
    )
    text = data.decode("utf-8")
    present = [line for line in imports if line in text]
    if present:
        raise RuntimeError(f"EQ337_CLOSED_PHYSICAL_CORE_IMPORT_EXISTS={present!r}")
    if not text.endswith("\n"):
        text += "\n"
    return (text + "".join(line + "\n" for line in imports)).encode("utf-8")


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

    require_commit(args.source_sha)
    require_prerequisites(args.source_sha)
    selected = paths()
    rows: list[tuple[str, bytes]] = []
    for scratch in selected:
        data = require_clean_blob(args.source_sha, scratch)
        target = destination(scratch)
        require_absent(args.source_sha, target)
        rows.append((target, retarget_imports(data)))

    core_status = git("status", "--porcelain=v1", "--", CORE)
    if core_status.returncode != 0 or core_status.stdout:
        raise RuntimeError("EQ337_CLOSED_PHYSICAL_CORE_DIRTY")
    rows.append((CORE, core_with_audits(git_blob(args.source_sha, CORE))))
    digest = manifest_digest(rows)

    if not args.apply:
        print(
            "EQ337_CLOSED_PHYSICAL_PROMOTION_PREVIEW_OK "
            f"files={len(rows)} promoted=6 source_sha={args.source_sha} "
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
                f"EQ337_CLOSED_PHYSICAL_POSTWRITE_MISMATCH={actual} WANT={digest}"
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
        "EQ337_CLOSED_PHYSICAL_PROMOTION_APPLY_OK "
        f"files={len(rows)} promoted=6 source_sha={args.source_sha} "
        f"manifest_sha256={digest}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
