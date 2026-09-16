#!/usr/bin/env python3
"""Fail-closed promotion of the source-facing C6d Eq. (3.60) wrapper.

This is instrumentation only.  It refuses to promote the two-file scratch
pair until every imported physical producer is present and sealed at one
immutable source commit.  Promotion retargets the five scratch imports,
preserves both PRE-VALIDATION notices, and adds only the audit to
``YangMillsCore``.
"""

from __future__ import annotations

import argparse
import hashlib
from pathlib import Path
import re
import subprocess


ROOT = Path(__file__).resolve().parents[1]
PATH_FILE = ROOT / "tmp" / "C6D-EQ360-LOCALIZED-RETAINED-DRAFT-PATHS.txt"
CORE = "YangMillsCore.lean"
EXPECTED_PATHS = 2
REQUIRED_PREREQUISITES = (
    "YangMills/RG/BalabanCMP99SourcePhysicalRealSliceTowerPair.lean",
    "YangMills/RG/BalabanCMP99Eq337ComplexClosedRadiusToPhysicalRadiusBudget.lean",
    "YangMills/RG/BalabanCMP99Eq360ComplexRegionalLaplacian.lean",
    "YangMills/RG/BalabanCMP99Eq360ComplexLocalLaplacianPerturbation.lean",
    "YangMills/RG/BalabanCMP99Eq360ComplexRegionalPrecisionPerturbation.lean",
    "YangMills/RG/BalabanCMP99Eq335PhysicalRegularityClassLocalizedPrecision.lean",
    "YangMills/RG/BalabanCMP99Eq337PhysicalComplexBaselineRealSlice.lean",
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
        raise RuntimeError("EQ360_C6D_SOURCE_SHA_INVALID")
    child = git("rev-parse", f"{source_sha}^{{commit}}")
    if child.returncode != 0 or child.stdout.decode().strip() != source_sha:
        raise RuntimeError("EQ360_C6D_SOURCE_COMMIT_MISMATCH")


def git_blob(source_sha: str, relative: str) -> bytes:
    child = git("cat-file", "blob", f"{source_sha}:{relative}")
    if child.returncode != 0:
        raise RuntimeError(
            f"EQ360_C6D_BLOB_FAILED={relative}:"
            + child.stderr.decode(errors="replace")
        )
    return child.stdout


def selected_paths() -> list[str]:
    rows = [
        line.strip()
        for line in PATH_FILE.read_text(encoding="utf-8").splitlines()
        if line.strip()
    ]
    if len(rows) != EXPECTED_PATHS or len(set(rows)) != EXPECTED_PATHS:
        raise RuntimeError(
            f"EQ360_C6D_SCOPE={len(rows)}/{len(set(rows))} "
            f"WANT={EXPECTED_PATHS}/{EXPECTED_PATHS}"
        )
    if any(
        not row.startswith("tmp/") or not row.endswith(".draft.lean")
        for row in rows
    ):
        raise RuntimeError("EQ360_C6D_SCOPE_PATH_INVALID")
    return rows


def destination(relative: str) -> str:
    name = Path(relative).name.removesuffix(".draft.lean")
    return f"YangMills/RG/{name}.lean"


def require_clean_blob(source_sha: str, relative: str) -> bytes:
    status = git("status", "--porcelain=v1", "--", relative)
    if status.returncode != 0 or status.stdout:
        raise RuntimeError(
            f"EQ360_C6D_DIRTY={relative}:"
            + status.stdout.decode(errors="replace").strip()
        )
    data = git_blob(source_sha, relative)
    worktree = (ROOT / relative).read_bytes().replace(b"\r\n", b"\n")
    if worktree != data:
        raise RuntimeError(f"EQ360_C6D_WORKTREE_DIVERGED={relative}")
    return data


def require_absent(source_sha: str, relative: str) -> None:
    status = git("status", "--porcelain=v1", "--", relative)
    if status.returncode != 0 or status.stdout:
        raise RuntimeError(f"EQ360_C6D_DESTINATION_DIRTY={relative}")
    probe = git("cat-file", "-e", f"{source_sha}:{relative}")
    if probe.returncode == 0 or (ROOT / relative).exists():
        raise RuntimeError(f"EQ360_C6D_DESTINATION_EXISTS={relative}")


def require_prerequisites(source_sha: str) -> None:
    for relative in REQUIRED_PREREQUISITES:
        data = git_blob(source_sha, relative)
        if b"PRE-VALIDATION:" in data:
            raise RuntimeError(f"EQ360_C6D_PREREQUISITE_UNSEALED={relative}")


def retarget_imports(data: bytes) -> bytes:
    text = data.decode("utf-8")
    text = re.sub(
        r"^import tmp\.([A-Za-z0-9_]+)\.draft$",
        r"import YangMills.RG.\1",
        text,
        flags=re.MULTILINE,
    )
    if "import tmp." in text:
        raise RuntimeError("EQ360_C6D_TMP_IMPORT_REMAINS")
    if text.count("PRE-VALIDATION:") != 1:
        raise RuntimeError("EQ360_C6D_PREVALIDATION_COUNT_MISMATCH")
    if re.search(r"(?m)^\s*axiom\b|\b(?:sorry|admit|by\?|exact\?)\b", text):
        raise RuntimeError("EQ360_C6D_FORBIDDEN_PLACEHOLDER")
    return text.encode("utf-8")


def core_with_audit(data: bytes, selected: list[str]) -> bytes:
    audits = [
        "import YangMills.RG." + Path(path).name.removesuffix(".draft.lean")
        for path in selected
        if Path(path).name.endswith("Audit.draft.lean")
    ]
    if len(audits) != 1:
        raise RuntimeError("EQ360_C6D_CORE_AUDIT_SCOPE")
    text = data.decode("utf-8")
    if audits[0] in text:
        raise RuntimeError("EQ360_C6D_CORE_IMPORT_EXISTS")
    if not text.endswith("\n"):
        text += "\n"
    return (text + audits[0] + "\n").encode("utf-8")


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
    selected = selected_paths()
    rows: list[tuple[str, bytes]] = []
    for scratch in selected:
        data = require_clean_blob(args.source_sha, scratch)
        target = destination(scratch)
        require_absent(args.source_sha, target)
        rows.append((target, retarget_imports(data)))

    core_status = git("status", "--porcelain=v1", "--", CORE)
    if core_status.returncode != 0 or core_status.stdout:
        raise RuntimeError("EQ360_C6D_CORE_DIRTY")
    rows.append((CORE, core_with_audit(git_blob(args.source_sha, CORE), selected)))
    digest = manifest_digest(rows)

    if not args.apply:
        print(
            "EQ360_C6D_PROMOTION_PREVIEW_OK "
            f"files={len(rows)} promoted={EXPECTED_PATHS} "
            f"source_sha={args.source_sha} manifest_sha256={digest}"
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
                f"EQ360_C6D_POSTWRITE_MISMATCH={actual} WANT={digest}"
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
        "EQ360_C6D_PROMOTION_APPLY_OK "
        f"files={len(rows)} promoted={EXPECTED_PATHS} "
        f"source_sha={args.source_sha} manifest_sha256={digest}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
