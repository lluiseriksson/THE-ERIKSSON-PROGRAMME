#!/usr/bin/env python3
"""Fail-closed selective seal for the six C6d source Green modules."""

from __future__ import annotations

import argparse
import hashlib
import importlib.util
from pathlib import Path
import subprocess
import sys


ROOT = Path(__file__).resolve().parents[1]
VERIFIER_PATH = (
    ROOT / "tmp" / "verify_c6d_source_separated_ambient_green_evidence.py"
)
PATH_MANIFEST = (
    ROOT / "tmp" / "c6d-source-separated-ambient-green-seal-paths.txt"
)
EXPECTED_EVIDENCE_SENTINEL = "C6D_SOURCE_SEPARATED_AMBIENT_GREEN_EVIDENCE_OK"


def load_verifier():
    spec = importlib.util.spec_from_file_location("c6d_source_green_verifier", VERIFIER_PATH)
    if spec is None or spec.loader is None:
        raise RuntimeError("C6D_SOURCE_GREEN_SEAL_VERIFIER_IMPORT_FAILED")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def run_git(*args: str) -> subprocess.CompletedProcess[bytes]:
    return subprocess.run(
        ["git", "-c", "safe.directory=*", *args],
        cwd=ROOT,
        check=False,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )


def scoped_paths(verifier) -> list[str]:
    paths = [
        line.strip()
        for line in PATH_MANIFEST.read_text(encoding="utf-8-sig").splitlines()
        if line.strip() and not line.lstrip().startswith("#")
    ]
    expected: list[str] = []
    for module in verifier.MODULES:
        expected.extend(
            [f"YangMills/RG/{module}.lean", f"YangMills/RG/{module}Audit.lean"]
        )
    if paths != expected or len(set(paths)) != len(expected):
        raise RuntimeError(f"C6D_SOURCE_GREEN_SEAL_SCOPE={paths!r}")
    return paths


def require_evidence(verifier, archive: Path, notebook: Path) -> None:
    child = subprocess.run(
        [sys.executable, str(VERIFIER_PATH), str(archive), str(notebook)],
        cwd=ROOT,
        check=False,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        text=True,
    )
    if child.returncode != 0:
        raise RuntimeError("C6D_SOURCE_GREEN_SEAL_EVIDENCE_FAILED=\n" + child.stdout)
    if EXPECTED_EVIDENCE_SENTINEL not in child.stdout:
        raise RuntimeError("C6D_SOURCE_GREEN_SEAL_EVIDENCE_SENTINEL_MISSING")
    if f"SOURCE_SHA={verifier.SOURCE_SHA}" not in child.stdout:
        raise RuntimeError("C6D_SOURCE_GREEN_SEAL_EVIDENCE_SOURCE_MISSING")


def require_exact_scope(paths: list[str], source_sha: str) -> None:
    for relative in paths:
        source_blob = run_git("rev-parse", f"{source_sha}:{relative}")
        head_blob = run_git("rev-parse", f"HEAD:{relative}")
        if source_blob.returncode != 0 or head_blob.returncode != 0:
            raise RuntimeError(f"C6D_SOURCE_GREEN_SEAL_BLOB_READ_FAILED={relative}")
        if source_blob.stdout.strip() != head_blob.stdout.strip():
            raise RuntimeError(f"C6D_SOURCE_GREEN_SEAL_HEAD_DIVERGED={relative}")
        status = run_git("status", "--porcelain=v1", "--", relative)
        if status.returncode != 0 or status.stdout:
            raise RuntimeError(
                f"C6D_SOURCE_GREEN_SEAL_WORKTREE_DIRTY={relative}:"
                + status.stdout.decode(errors="replace").strip()
            )


def transformed_bytes(relative: str, source_sha: str) -> tuple[bytes, bytes]:
    path = ROOT / relative
    original = path.read_bytes()
    blob = run_git("show", f"{source_sha}:{relative}")
    if blob.returncode != 0:
        raise RuntimeError(f"C6D_SOURCE_GREEN_SEAL_SOURCE_READ_FAILED={relative}")
    canonical = blob.stdout
    if b"\r\n" in canonical:
        raise RuntimeError(f"C6D_SOURCE_GREEN_SEAL_SOURCE_CRLF={relative}")
    if canonical.count(b"PRE-VALIDATION") != 1:
        raise RuntimeError(
            f"C6D_SOURCE_GREEN_SEAL_PRE_COUNT={relative}:"
            f"{canonical.count(b'PRE-VALIDATION')}"
        )
    marker = canonical.index(b"PRE-VALIDATION")
    start = canonical.rfind(b"/-!", 0, marker)
    end = canonical.find(b"-/", marker)
    if start < 0 or end < 0:
        raise RuntimeError(f"C6D_SOURCE_GREEN_SEAL_NOTICE_BOUNDS={relative}")
    end += 2
    while end < len(canonical) and canonical[end:end + 1] in {b"\r", b"\n"}:
        end += 1
    sealed = canonical[:start] + canonical[end:]
    if b"PRE-VALIDATION" in sealed:
        raise RuntimeError(f"C6D_SOURCE_GREEN_SEAL_PRE_REMAINS={relative}")
    return original, sealed


def manifest_digest(rows: list[tuple[str, bytes]]) -> str:
    canonical = b"".join(
        f"{hashlib.sha256(data).hexdigest().upper()}  {relative}\n".encode()
        for relative, data in rows
    )
    return hashlib.sha256(canonical).hexdigest().upper()


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("archive", type=Path)
    parser.add_argument("executed_notebook", type=Path)
    parser.add_argument("--apply", action="store_true")
    args = parser.parse_args()
    verifier = load_verifier()
    paths = scoped_paths(verifier)
    require_evidence(verifier, args.archive.resolve(), args.executed_notebook.resolve())
    require_exact_scope(paths, verifier.SOURCE_SHA)

    originals: dict[str, bytes] = {}
    sealed_rows: list[tuple[str, bytes]] = []
    for relative in paths:
        original, sealed = transformed_bytes(relative, verifier.SOURCE_SHA)
        originals[relative] = original
        sealed_rows.append((relative, sealed))
    expected_digest = manifest_digest(sealed_rows)
    if not args.apply:
        print(
            "C6D_SOURCE_SEPARATED_AMBIENT_GREEN_SEAL_PREVIEW_OK "
            f"files={len(paths)} source_sha={verifier.SOURCE_SHA} "
            f"sealed_manifest_sha256={expected_digest}"
        )
        return 0

    written: list[str] = []
    try:
        for relative, sealed in sealed_rows:
            (ROOT / relative).write_bytes(sealed)
            written.append(relative)
        actual = manifest_digest(
            [(relative, (ROOT / relative).read_bytes()) for relative in paths]
        )
        if actual != expected_digest:
            raise RuntimeError(
                f"C6D_SOURCE_GREEN_SEAL_POSTWRITE_DIGEST={actual} "
                f"EXPECTED={expected_digest}"
            )
    except Exception:
        for relative in reversed(written):
            (ROOT / relative).write_bytes(originals[relative])
        raise

    print(
        "C6D_SOURCE_SEPARATED_AMBIENT_GREEN_SEAL_APPLY_OK "
        f"files={len(paths)} source_sha={verifier.SOURCE_SHA} "
        f"sealed_manifest_sha256={expected_digest}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
