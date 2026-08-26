#!/usr/bin/env python3
"""Remove PRE-VALIDATION only after exact Eq. (3.59) real-slice evidence."""

from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import subprocess


ROOT = Path(__file__).resolve().parents[1]
BASE_SEALER = ROOT / "tmp" / "seal_eq337_complex_perturbed_background_prevalidation.py"
CONTRACT_PATH = ROOT / "tmp" / "verify_eq359_real_slice_contract.py"


def load(path: Path, name: str):
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"EQ359_REAL_SLICE_SEAL_MODULE_LOAD_FAILED={path}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def git(*args: str) -> subprocess.CompletedProcess[bytes]:
    return subprocess.run(
        ["git", "-c", "safe.directory=*", *args],
        cwd=ROOT,
        check=False,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )


def git_blob(source_sha: str, relative: str) -> bytes:
    child = git("cat-file", "blob", f"{source_sha}:{relative}")
    if child.returncode != 0:
        raise RuntimeError(
            f"EQ359_REAL_SLICE_SEAL_BLOB_FAILED={relative}:"
            + child.stderr.decode(errors="replace")
        )
    return child.stdout


def read_evidence(path: Path) -> dict:
    result = json.loads(path.read_text(encoding="utf-8"))
    if result.get("status") != "EQ359_REAL_SLICE_EVIDENCE_OK":
        raise RuntimeError("EQ359_REAL_SLICE_SEAL_STATUS_MISMATCH")
    if result.get("expected_declarations") != 24:
        raise RuntimeError("EQ359_REAL_SLICE_SEAL_DECLARATIONS_MISMATCH")
    source_sha = result.get("source_sha")
    if not isinstance(source_sha, str) or re.fullmatch(r"[0-9a-f]{40}", source_sha) is None:
        raise RuntimeError("EQ359_REAL_SLICE_SEAL_SOURCE_INVALID")
    if not isinstance(result.get("boundary_blob_sha256"), dict):
        raise RuntimeError("EQ359_REAL_SLICE_SEAL_HASHES_MISSING")
    return result


def paths(contract) -> list[str]:
    rows = [
        f"YangMills/RG/{module}{suffix}.lean"
        for module, _ in contract.MODULES
        for suffix in ("", "Audit")
    ]
    if len(rows) != 10 or len(set(rows)) != 10:
        raise RuntimeError("EQ359_REAL_SLICE_SEAL_SCOPE_INVALID")
    return rows


def require_clean_exact(result: dict, relative: str) -> bytes:
    source_sha = result["source_sha"]
    status = git("status", "--porcelain=v1", "--", relative)
    if status.returncode != 0 or status.stdout:
        raise RuntimeError(f"EQ359_REAL_SLICE_SEAL_DIRTY={relative}")
    data = git_blob(source_sha, relative)
    wanted = result["boundary_blob_sha256"].get(relative)
    measured = hashlib.sha256(data).hexdigest()
    if wanted != measured:
        raise RuntimeError(
            f"EQ359_REAL_SLICE_SEAL_EVIDENCE_MISMATCH={relative}:"
            f"{measured}:{wanted}"
        )
    worktree = (ROOT / relative).read_bytes().replace(b"\r\n", b"\n")
    if worktree != data:
        raise RuntimeError(f"EQ359_REAL_SLICE_SEAL_WORKTREE_DIVERGED={relative}")
    return data


def digest(rows: list[tuple[str, bytes]]) -> str:
    payload = b"".join(
        f"{hashlib.sha256(data).hexdigest().upper()}  {relative}\n".encode()
        for relative, data in rows
    )
    return hashlib.sha256(payload).hexdigest().upper()


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--evidence-json", type=Path, required=True)
    parser.add_argument("--apply", action="store_true")
    args = parser.parse_args()

    result = read_evidence(args.evidence_json.resolve())
    remover = load(BASE_SEALER, "eq359_real_slice_notice_remover")
    contract = load(CONTRACT_PATH, "eq359_real_slice_seal_contract")
    rows = [
        (
            relative,
            remover.remove_prevalidation_block(
                require_clean_exact(result, relative), relative
            ),
        )
        for relative in paths(contract)
    ]
    manifest_sha = digest(rows)
    if not args.apply:
        print(
            "EQ359_REAL_SLICE_SEAL_PREVIEW_OK "
            f"files=10 source_sha={result['source_sha']} "
            f"manifest_sha256={manifest_sha}"
        )
        return 0

    originals = {relative: (ROOT / relative).read_bytes() for relative, _ in rows}
    written: list[str] = []
    try:
        for relative, data in rows:
            (ROOT / relative).write_bytes(data)
            written.append(relative)
        for relative, _ in rows:
            if "PRE-VALIDATION:" in (ROOT / relative).read_text(encoding="utf-8-sig"):
                raise RuntimeError(f"EQ359_REAL_SLICE_PREVALIDATION_REMAINS={relative}")
        actual = digest(
            [(relative, (ROOT / relative).read_bytes()) for relative, _ in rows]
        )
        if actual != manifest_sha:
            raise RuntimeError(
                f"EQ359_REAL_SLICE_SEAL_POSTWRITE_MISMATCH={actual}"
            )
    except Exception:
        for relative in reversed(written):
            (ROOT / relative).write_bytes(originals[relative])
        raise

    print(
        "EQ359_REAL_SLICE_SEAL_APPLY_OK "
        f"files=10 source_sha={result['source_sha']} "
        f"manifest_sha256={manifest_sha}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
