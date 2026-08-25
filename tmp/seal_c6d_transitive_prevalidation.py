#!/usr/bin/env python3
"""Fail-closed removal of the C6d transitive PRE-VALIDATION boundary.

The script is a mechanical seal helper.  It refuses to act unless every one
of the 34 tracked source/audit paths is unchanged from the exact checkpoint
compiled by the cold C6d runner.  Its default mode is read-only; ``--apply``
removes only the two-line PRE notice and any module-doc block left empty by
that removal.  On a write or verification failure all touched files are
restored byte-for-byte.
"""

from __future__ import annotations

import argparse
import hashlib
import importlib.util
import re
import subprocess
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
VERIFIER = ROOT / "tmp" / "verify_c6d_root_transitive_axioms.py"
PRE_MARKER = (
    "PRE-VALIDATION: source is present in scratch only; no `.olean` has been\n"
    "materialized and no compiler or axiom-oracle verdict exists for this module."
)
EMPTY_MODULE_DOC = re.compile(r"(?m)^/-!\n[ \t]*\n-/\n?")


def load_verifier():
    spec = importlib.util.spec_from_file_location("c6d_axiom_verifier", VERIFIER)
    if spec is None or spec.loader is None:
        raise RuntimeError("C6D_VERIFIER_IMPORT_FAILED")
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


def boundary_paths(verifier) -> list[str]:
    paths: list[str] = []
    for module in verifier.MODULES:
        paths.extend(
            (
                f"YangMills/RG/{module}.lean",
                f"YangMills/RG/{module}Audit.lean",
            )
        )
    if len(paths) != 34 or len(set(paths)) != 34:
        raise RuntimeError(f"C6D_BOUNDARY_SCOPE={len(paths)}/{len(set(paths))}")
    return paths


def require_exact_checkpoint(paths: list[str], source_sha: str) -> None:
    for relative in paths:
        child = run_git("diff", "--quiet", source_sha, "--", relative)
        if child.returncode != 0:
            raise RuntimeError(f"C6D_BOUNDARY_DIVERGED={relative}")
        status = run_git("status", "--porcelain=v1", "--", relative)
        if status.returncode != 0:
            raise RuntimeError(
                f"C6D_BOUNDARY_STATUS_FAILED={relative} "
                f"stderr={status.stderr.decode(errors='replace')}"
            )
        if status.stdout:
            raise RuntimeError(
                f"C6D_BOUNDARY_WORKTREE_DIRTY={relative} "
                f"status={status.stdout.decode(errors='replace').strip()}"
            )


def transformed_bytes(relative: str, source_sha: str) -> tuple[bytes, bytes]:
    path = ROOT / relative
    original = path.read_bytes()
    blob = run_git("show", f"{source_sha}:{relative}")
    if blob.returncode != 0:
        raise RuntimeError(
            f"C6D_SOURCE_BLOB_READ_FAILED={relative} "
            f"stderr={blob.stderr.decode(errors='replace')}"
        )
    # The seal manifest is defined over canonical Git bytes, not over the
    # checkout's core.autocrlf-dependent worktree representation.
    text = blob.stdout.decode("utf-8")
    if "\r\n" in text:
        raise RuntimeError(f"C6D_SOURCE_BLOB_CRLF={relative}")
    count = text.count(PRE_MARKER)
    if count != 1:
        raise RuntimeError(f"C6D_PRE_MARKER_COUNT={relative}:{count}")
    sealed = text.replace(PRE_MARKER, "", 1)
    sealed = EMPTY_MODULE_DOC.sub("", sealed, count=1)
    if "PRE-VALIDATION:" in sealed:
        raise RuntimeError(f"C6D_PRE_MARKER_REMAINS={relative}")
    if EMPTY_MODULE_DOC.search(sealed):
        raise RuntimeError(f"C6D_EMPTY_MODULE_DOC_REMAINS={relative}")
    return original, sealed.encode("utf-8")


def digest(rows: list[tuple[str, bytes]]) -> str:
    payload = b"".join(
        f"{hashlib.sha256(data).hexdigest().upper()}  {relative}\n".encode()
        for relative, data in rows
    )
    return hashlib.sha256(payload).hexdigest().upper()


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--apply", action="store_true")
    args = parser.parse_args()

    verifier = load_verifier()
    paths = boundary_paths(verifier)
    require_exact_checkpoint(paths, verifier.SOURCE_SHA)
    originals: dict[str, bytes] = {}
    sealed_rows: list[tuple[str, bytes]] = []
    for relative in paths:
        original, sealed = transformed_bytes(relative, verifier.SOURCE_SHA)
        originals[relative] = original
        sealed_rows.append((relative, sealed))

    manifest_sha = digest(sealed_rows)
    if not args.apply:
        print(
            "C6D_TRANSITIVE_SEAL_PREVIEW_OK "
            f"files={len(paths)} source_sha={verifier.SOURCE_SHA} "
            f"sealed_manifest_sha256={manifest_sha}"
        )
        return 0

    written: list[str] = []
    try:
        for relative, sealed in sealed_rows:
            (ROOT / relative).write_bytes(sealed)
            written.append(relative)
        for relative in paths:
            current = (ROOT / relative).read_text(encoding="utf-8-sig")
            if "PRE-VALIDATION:" in current:
                raise RuntimeError(f"C6D_POSTWRITE_PRE_REMAINS={relative}")
        actual = digest([(relative, (ROOT / relative).read_bytes()) for relative in paths])
        if actual != manifest_sha:
            raise RuntimeError(
                f"C6D_POSTWRITE_MANIFEST_MISMATCH={actual} WANT={manifest_sha}"
            )
    except Exception:
        for relative in reversed(written):
            (ROOT / relative).write_bytes(originals[relative])
        raise

    print(
        "C6D_TRANSITIVE_SEAL_APPLY_OK "
        f"files={len(paths)} source_sha={verifier.SOURCE_SHA} "
        f"sealed_manifest_sha256={manifest_sha}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
