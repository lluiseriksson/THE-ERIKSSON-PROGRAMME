#!/usr/bin/env python3
"""Legacy regional evidence reader; notice removal is intentionally disabled.

The regional scope overlaps the ten-file physical Eq. (3.60) gate.  The live
fail-closed route seals the disjoint adjoint-composition pair first and then
uses ``seal_eq360_complex_physical_prevalidation.py`` for the ten Eq. (3.60)
files.  Keeping this module readable preserves old evidence tooling without
leaving a second writer for the same PRE-VALIDATION notices.
"""

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
CONTRACT_PATH = ROOT / "tmp" / "verify_eq360_complex_regional_contract.py"


def load(path: Path, name: str):
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"EQ360_COMPLEX_REGIONAL_SEAL_MODULE_LOAD_FAILED={path}")
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
            f"EQ360_COMPLEX_REGIONAL_SEAL_BLOB_FAILED={relative}:"
            + child.stderr.decode(errors="replace")
        )
    return child.stdout


def read_evidence(path: Path) -> dict:
    result = json.loads(path.read_text(encoding="utf-8"))
    if result.get("status") != "EQ360_COMPLEX_REGIONAL_EVIDENCE_OK":
        raise RuntimeError("EQ360_COMPLEX_REGIONAL_SEAL_STATUS_MISMATCH")
    if result.get("expected_declarations") != 18:
        raise RuntimeError("EQ360_COMPLEX_REGIONAL_SEAL_DECLARATIONS_MISMATCH")
    source_sha = result.get("source_sha")
    if not isinstance(source_sha, str) or re.fullmatch(r"[0-9a-f]{40}", source_sha) is None:
        raise RuntimeError("EQ360_COMPLEX_REGIONAL_SEAL_SOURCE_INVALID")
    if not isinstance(result.get("boundary_blob_sha256"), dict):
        raise RuntimeError("EQ360_COMPLEX_REGIONAL_SEAL_HASHES_MISSING")
    return result


def paths(contract) -> list[str]:
    rows = [
        f"YangMills/RG/{module}{suffix}.lean"
        for module, _ in contract.MODULES
        for suffix in ("", "Audit")
    ]
    if len(rows) != 8 or len(set(rows)) != 8:
        raise RuntimeError("EQ360_COMPLEX_REGIONAL_SEAL_SCOPE_INVALID")
    return rows


def require_clean_exact(result: dict, relative: str) -> bytes:
    status = git("status", "--porcelain=v1", "--", relative)
    if status.returncode != 0 or status.stdout:
        raise RuntimeError(f"EQ360_COMPLEX_REGIONAL_SEAL_DIRTY={relative}")
    data = git_blob(result["source_sha"], relative)
    wanted = result["boundary_blob_sha256"].get(relative)
    measured = hashlib.sha256(data).hexdigest()
    if wanted != measured:
        raise RuntimeError(
            f"EQ360_COMPLEX_REGIONAL_SEAL_EVIDENCE_MISMATCH={relative}:"
            f"{measured}:{wanted}"
        )
    worktree = (ROOT / relative).read_bytes().replace(b"\r\n", b"\n")
    if worktree != data:
        raise RuntimeError(
            f"EQ360_COMPLEX_REGIONAL_SEAL_WORKTREE_DIVERGED={relative}"
        )
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
    raise RuntimeError(
        "EQ360_COMPLEX_REGIONAL_SEAL_SUPERSEDED="
        "seal_eq351_adjoint_composition_prevalidation.py+"
        "seal_eq360_complex_physical_prevalidation.py"
    )
    result = read_evidence(args.evidence_json.resolve())
    remover = load(BASE_SEALER, "eq360_complex_regional_notice_remover")
    contract = load(CONTRACT_PATH, "eq360_complex_regional_seal_contract")
    original_rows = [
        (relative, require_clean_exact(result, relative))
        for relative in paths(contract)
    ]
    notice_count = sum(
        data.count(b"PRE-VALIDATION:") for _, data in original_rows
    )
    if notice_count != 8:
        raise RuntimeError(
            f"EQ360_COMPLEX_REGIONAL_SEAL_NOTICE_COUNT_MISMATCH={notice_count}:8"
        )
    rows = [
        (relative, remover.remove_prevalidation_block(data, relative))
        for relative, data in original_rows
    ]
    manifest_sha = digest(rows)
    if not args.apply:
        print(
            "EQ360_COMPLEX_REGIONAL_SEAL_PREVIEW_OK "
            f"files=8 notices={notice_count} source_sha={result['source_sha']} "
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
            if "PRE-VALIDATION:" in (ROOT / relative).read_text(
                encoding="utf-8-sig"
            ):
                raise RuntimeError(
                    f"EQ360_COMPLEX_REGIONAL_PREVALIDATION_REMAINS={relative}"
                )
        actual = digest(
            [(relative, (ROOT / relative).read_bytes()) for relative, _ in rows]
        )
        if actual != manifest_sha:
            raise RuntimeError(
                f"EQ360_COMPLEX_REGIONAL_SEAL_POSTWRITE_MISMATCH={actual}"
            )
    except Exception:
        for relative in reversed(written):
            (ROOT / relative).write_bytes(originals[relative])
        raise

    print(
        "EQ360_COMPLEX_REGIONAL_SEAL_APPLY_OK "
        f"files=8 notices={notice_count} source_sha={result['source_sha']} "
        f"manifest_sha256={manifest_sha}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
