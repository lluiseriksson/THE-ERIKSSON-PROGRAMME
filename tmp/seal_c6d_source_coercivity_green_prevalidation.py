#!/usr/bin/env python3
"""Fail-closed seal helper for the C6d source coercivity/Green gate.

The default mode is read-only.  ``--apply`` removes only the exact
PRE-VALIDATION module notice from the twenty source/audit blobs compiled by
the cold gate.  The helper refuses to act unless:

* the cold archive and the original one-code-cell executed notebook pass the
  independent evidence verifier;
* every scoped path is byte-identical in Git to the compiled source SHA;
* none of those paths has an uncommitted worktree change; and
* each path contains exactly one sanctioned PRE-VALIDATION notice.

On a write or post-write verification failure every touched path is restored
byte-for-byte.  Documentation and evidence-ledger edits remain deliberately
outside this mechanical source seal.
"""

from __future__ import annotations

import argparse
import hashlib
import importlib.util
import re
import subprocess
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
VERIFIER_PATH = ROOT / "tmp" / "verify_c6d_source_coercivity_green_evidence.py"
PATH_MANIFEST = ROOT / "tmp" / "c6d-source-coercivity-green-seal-paths.txt"

PRE_NOTICE = re.compile(
    rb"/-!\n"
    rb"PRE-VALIDATION: this module's source is present, its `\.olean` has not yet\n"
    rb"been materialized, and its result has not yet been verified by the compiler\.\n"
    rb"-/\n"
)


def load_verifier():
    spec = importlib.util.spec_from_file_location("c6d_cold_verifier", VERIFIER_PATH)
    if spec is None or spec.loader is None:
        raise RuntimeError("C6D_SEAL_VERIFIER_IMPORT_FAILED")
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
            (
                f"YangMills/RG/{module}.lean",
                f"YangMills/RG/{module}Audit.lean",
            )
        )
    if len(paths) != 20 or len(set(paths)) != 20 or paths != expected:
        raise RuntimeError(
            "C6D_SEAL_SCOPE="
            f"paths={len(paths)}/{len(set(paths))} expected={len(expected)}"
        )
    return paths


def require_evidence(verifier, archive: Path, notebook: Path) -> None:
    if not archive.is_file():
        raise RuntimeError(f"C6D_SEAL_ARCHIVE_MISSING={archive}")
    if not notebook.is_file():
        raise RuntimeError(f"C6D_SEAL_NOTEBOOK_MISSING={notebook}")
    child = subprocess.run(
        [sys.executable, str(VERIFIER_PATH), str(archive), str(notebook)],
        cwd=ROOT,
        check=False,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        text=True,
    )
    if child.returncode != 0:
        raise RuntimeError("C6D_SEAL_EVIDENCE_FAILED=\n" + child.stdout)
    if "C6D_SOURCE_COERCIVITY_GREEN_EVIDENCE_OK" not in child.stdout:
        raise RuntimeError("C6D_SEAL_EVIDENCE_SENTINEL_MISSING")
    expected_source = f"SOURCE_SHA={verifier.SOURCE_SHA}"
    if expected_source not in child.stdout:
        raise RuntimeError(
            "C6D_SEAL_EVIDENCE_SOURCE_MISSING=" + expected_source
        )


def require_exact_scope(paths: list[str], source_sha: str) -> None:
    for relative in paths:
        source_blob = run_git("rev-parse", f"{source_sha}:{relative}")
        head_blob = run_git("rev-parse", f"HEAD:{relative}")
        if source_blob.returncode != 0 or head_blob.returncode != 0:
            raise RuntimeError(f"C6D_SEAL_BLOB_READ_FAILED={relative}")
        if source_blob.stdout.strip() != head_blob.stdout.strip():
            raise RuntimeError(f"C6D_SEAL_HEAD_DIVERGED={relative}")
        status = run_git("status", "--porcelain=v1", "--", relative)
        if status.returncode != 0:
            raise RuntimeError(f"C6D_SEAL_STATUS_FAILED={relative}")
        if status.stdout:
            raise RuntimeError(
                f"C6D_SEAL_WORKTREE_DIRTY={relative}:"
                + status.stdout.decode(errors="replace").strip()
            )


def transformed_bytes(relative: str, source_sha: str) -> tuple[bytes, bytes]:
    path = ROOT / relative
    original = path.read_bytes()
    blob = run_git("show", f"{source_sha}:{relative}")
    if blob.returncode != 0:
        raise RuntimeError(f"C6D_SEAL_SOURCE_BLOB_READ_FAILED={relative}")
    canonical = blob.stdout
    if b"\r\n" in canonical:
        raise RuntimeError(f"C6D_SEAL_SOURCE_BLOB_CRLF={relative}")
    matches = list(PRE_NOTICE.finditer(canonical))
    if len(matches) != 1:
        raise RuntimeError(f"C6D_SEAL_PRE_NOTICE_COUNT={relative}:{len(matches)}")
    sealed = PRE_NOTICE.sub(b"", canonical, count=1)
    if b"PRE-VALIDATION" in sealed:
        raise RuntimeError(f"C6D_SEAL_PRE_NOTICE_REMAINS={relative}")
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
    require_evidence(
        verifier,
        args.archive.resolve(),
        args.executed_notebook.resolve(),
    )
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
            "C6D_SOURCE_COERCIVITY_GREEN_SEAL_PREVIEW_OK "
            f"files={len(paths)} source_sha={verifier.SOURCE_SHA} "
            f"sealed_manifest_sha256={expected_digest}"
        )
        return 0

    written: list[str] = []
    try:
        for relative, sealed in sealed_rows:
            (ROOT / relative).write_bytes(sealed)
            written.append(relative)
        for relative in paths:
            current = (ROOT / relative).read_bytes()
            if b"PRE-VALIDATION" in current:
                raise RuntimeError(f"C6D_SEAL_POSTWRITE_PRE_REMAINS={relative}")
        actual_digest = manifest_digest(
            [(relative, (ROOT / relative).read_bytes()) for relative in paths]
        )
        if actual_digest != expected_digest:
            raise RuntimeError(
                "C6D_SEAL_POSTWRITE_DIGEST="
                f"{actual_digest} EXPECTED={expected_digest}"
            )
    except Exception:
        for relative in reversed(written):
            (ROOT / relative).write_bytes(originals[relative])
        raise

    print(
        "C6D_SOURCE_COERCIVITY_GREEN_SEAL_APPLY_OK "
        f"files={len(paths)} source_sha={verifier.SOURCE_SHA} "
        f"sealed_manifest_sha256={expected_digest}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
