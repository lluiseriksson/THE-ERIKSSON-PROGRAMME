#!/usr/bin/env python3
"""Mechanically seal the six-file Eq. (3.37) complex-coordinate boundary."""

from __future__ import annotations

import argparse
import hashlib
import importlib.util
import re
import subprocess
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
VERIFIER = ROOT / "tmp" / "verify_eq337_complex_coordinate_evidence.py"
CORE = "YangMillsCore.lean"
CORE_BLOB_SHA256 = "dabba854357f0abf6b2d994e5a96efc8271358d6c45c66dea9a087cfa4bb2479"
DOC_BLOCK = re.compile(r"/-![\s\S]*?-/")


def load_verifier():
    spec = importlib.util.spec_from_file_location("eq337_evidence_verifier", VERIFIER)
    if spec is None or spec.loader is None:
        raise RuntimeError("EQ337_VERIFIER_IMPORT_FAILED")
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


def git_blob(source_sha: str, relative: str) -> bytes:
    child = run_git("show", f"{source_sha}:{relative}")
    if child.returncode != 0:
        raise RuntimeError(
            f"EQ337_SOURCE_BLOB_READ_FAILED={relative} "
            f"stderr={child.stderr.decode(errors='replace')}"
        )
    return child.stdout


def boundary_paths(verifier) -> list[str]:
    paths: list[str] = []
    for module in verifier.MODULES:
        paths.extend(
            (f"YangMills/RG/{module}.lean", f"YangMills/RG/{module}Audit.lean")
        )
    if len(paths) != 6 or len(set(paths)) != 6:
        raise RuntimeError(f"EQ337_BOUNDARY_SCOPE={len(paths)}/{len(set(paths))}")
    return paths


def require_clean_exact(paths: list[str], source_sha: str) -> None:
    for relative in [*paths, CORE]:
        status = run_git("status", "--porcelain=v1", "--", relative)
        if status.returncode != 0 or status.stdout:
            raise RuntimeError(
                f"EQ337_WORKTREE_DIRTY={relative} "
                f"status={status.stdout.decode(errors='replace').strip()}"
            )
    for relative in paths:
        child = run_git("diff", "--quiet", source_sha, "--", relative)
        if child.returncode != 0:
            raise RuntimeError(f"EQ337_BOUNDARY_DIVERGED={relative}")
    core = git_blob(source_sha, CORE)
    measured = hashlib.sha256(core).hexdigest()
    if measured != CORE_BLOB_SHA256:
        raise RuntimeError(f"EQ337_CORE_BLOB_MISMATCH={measured}")
    if (ROOT / CORE).read_bytes().replace(b"\r\n", b"\n") != core:
        raise RuntimeError("EQ337_CORE_WORKTREE_BYTES_DIVERGED")


def remove_prevalidation_block(data: bytes, relative: str) -> bytes:
    text = data.decode("utf-8")
    blocks = [match for match in DOC_BLOCK.finditer(text) if "PRE-VALIDATION:" in match.group()]
    if len(blocks) != 1:
        raise RuntimeError(f"EQ337_PREVALIDATION_BLOCK_COUNT={relative}:{len(blocks)}")
    match = blocks[0]
    block = match.group()
    body = block[3:-2]
    lines = body.splitlines(keepends=True)
    indices = [i for i, line in enumerate(lines) if "PRE-VALIDATION:" in line]
    if len(indices) != 1:
        raise RuntimeError(f"EQ337_PREVALIDATION_LINE_COUNT={relative}:{len(indices)}")
    start = indices[0]
    end = start + 1
    while end < len(lines) and lines[end].strip():
        end += 1
    if end < len(lines) and not lines[end].strip():
        end += 1
    remainder = "".join(lines[:start] + lines[end:])
    replacement = "" if not remainder.strip() else "/-!" + remainder + "-/"
    sealed = text[: match.start()] + replacement + text[match.end() :]
    sealed = re.sub(r"\n{3,}(?=#print axioms)", "\n\n", sealed, count=1)
    if "PRE-VALIDATION:" in sealed:
        raise RuntimeError(f"EQ337_PREVALIDATION_REMAINS={relative}")
    return sealed.encode("utf-8")


def sealed_core(data: bytes, verifier) -> bytes:
    text = data.decode("utf-8")
    imports = [f"import YangMills.RG.{module}Audit" for module in verifier.MODULES]
    present = [line for line in imports if line in text]
    if present:
        raise RuntimeError(f"EQ337_CORE_IMPORT_ALREADY_PRESENT={present!r}")
    if not text.endswith("\n"):
        text += "\n"
    text += "".join(line + "\n" for line in imports)
    return text.encode("utf-8")


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
    require_clean_exact(paths, verifier.SOURCE_SHA)
    rows = [
        (relative, remove_prevalidation_block(git_blob(verifier.SOURCE_SHA, relative), relative))
        for relative in paths
    ]
    rows.append((CORE, sealed_core(git_blob(verifier.SOURCE_SHA, CORE), verifier)))
    manifest_sha = digest(rows)
    if not args.apply:
        print(
            "EQ337_COMPLEX_COORDINATE_SEAL_PREVIEW_OK "
            f"files={len(rows)} source_sha={verifier.SOURCE_SHA} "
            f"sealed_manifest_sha256={manifest_sha}"
        )
        return 0

    originals = {relative: (ROOT / relative).read_bytes() for relative, _ in rows}
    written: list[str] = []
    try:
        for relative, data in rows:
            (ROOT / relative).write_bytes(data)
            written.append(relative)
        actual = digest([(relative, (ROOT / relative).read_bytes()) for relative, _ in rows])
        if actual != manifest_sha:
            raise RuntimeError(f"EQ337_POSTWRITE_MANIFEST_MISMATCH={actual}")
    except Exception:
        for relative in reversed(written):
            (ROOT / relative).write_bytes(originals[relative])
        raise

    print(
        "EQ337_COMPLEX_COORDINATE_SEAL_APPLY_OK "
        f"files={len(rows)} source_sha={verifier.SOURCE_SHA} "
        f"sealed_manifest_sha256={manifest_sha}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
