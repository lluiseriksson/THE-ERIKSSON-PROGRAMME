#!/usr/bin/env python3
"""Remove PRE-VALIDATION only after exact next C6d real-slice archive evidence.

The raw archive is reverified inside this process against the immutable
source and runner pins.  A caller-supplied verifier JSON is deliberately not
accepted as authority for the write gate.
"""

from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import tempfile


ROOT = Path(__file__).resolve().parents[1]
BASE_SEALER = ROOT / "tmp" / "seal_eq337_complex_perturbed_background_prevalidation.py"
CONTRACT_PATH = ROOT / "tmp" / "verify_c6d_next_real_slice_contract.py"
ARCHIVE_VERIFIER = ROOT / "tmp" / "verify_c6d_next_real_slice_archive.py"
SOURCE_SHA = "81cc22e41d46cce150c2a263c85e4acb90087153"
RUNNER_REV = "c6d-next-real-slice-v1"


def load(path: Path, name: str):
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"C6D_NEXT_REAL_SLICE_SEAL_MODULE_LOAD_FAILED={path}")
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
            f"C6D_NEXT_REAL_SLICE_SEAL_BLOB_FAILED={relative}:"
            + child.stderr.decode(errors="replace")
        )
    return child.stdout


def verify_archive(path: Path) -> dict:
    if not path.is_file():
        raise RuntimeError("C6D_NEXT_REAL_SLICE_SEAL_ARCHIVE_MISSING")
    with tempfile.TemporaryDirectory(prefix="c6d-next-real-slice-seal-") as temp:
        verification_json = Path(temp) / "verification.json"
        child = subprocess.run(
            [
                sys.executable,
                str(ARCHIVE_VERIFIER),
                "--repo",
                str(ROOT),
                "--archive",
                str(path),
                "--source-sha",
                SOURCE_SHA,
                "--runner-rev",
                RUNNER_REV,
                "--json-out",
                str(verification_json),
            ],
            cwd=ROOT,
            check=False,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            text=True,
        )
        if child.returncode != 0:
            raise RuntimeError(
                "C6D_NEXT_REAL_SLICE_SEAL_ARCHIVE_VERIFIER_FAILED=" + child.stdout
            )
        result = json.loads(verification_json.read_text(encoding="utf-8"))
    if result.get("status") != "C6D_NEXT_REAL_SLICE_EVIDENCE_OK":
        raise RuntimeError("C6D_NEXT_REAL_SLICE_SEAL_STATUS_MISMATCH")
    if result.get("expected_declarations") != 10:
        raise RuntimeError("C6D_NEXT_REAL_SLICE_SEAL_DECLARATIONS_MISMATCH")
    source_sha = result.get("source_sha")
    if source_sha != SOURCE_SHA:
        raise RuntimeError("C6D_NEXT_REAL_SLICE_SEAL_SOURCE_MISMATCH")
    if result.get("runner_revision") != RUNNER_REV:
        raise RuntimeError("C6D_NEXT_REAL_SLICE_SEAL_RUNNER_MISMATCH")
    if not isinstance(result.get("boundary_blob_sha256"), dict):
        raise RuntimeError("C6D_NEXT_REAL_SLICE_SEAL_HASHES_MISSING")
    return result


def paths(contract) -> list[str]:
    rows = [
        f"YangMills/RG/{module}{suffix}.lean"
        for module, _ in contract.MODULES
        for suffix in ("", "Audit")
    ]
    if len(rows) != 6 or len(set(rows)) != 6:
        raise RuntimeError("C6D_NEXT_REAL_SLICE_SEAL_SCOPE_INVALID")
    return rows


def require_clean_exact(result: dict, relative: str) -> bytes:
    source_sha = result["source_sha"]
    status = git("status", "--porcelain=v1", "--", relative)
    if status.returncode != 0 or status.stdout:
        raise RuntimeError(f"C6D_NEXT_REAL_SLICE_SEAL_DIRTY={relative}")
    data = git_blob(source_sha, relative)
    wanted = result["boundary_blob_sha256"].get(relative)
    measured = hashlib.sha256(data).hexdigest()
    if wanted != measured:
        raise RuntimeError(
            f"C6D_NEXT_REAL_SLICE_SEAL_EVIDENCE_MISMATCH={relative}:"
            f"{measured}:{wanted}"
        )
    worktree = (ROOT / relative).read_bytes().replace(b"\r\n", b"\n")
    if worktree != data:
        raise RuntimeError(f"C6D_NEXT_REAL_SLICE_SEAL_WORKTREE_DIVERGED={relative}")
    return data


def digest(rows: list[tuple[str, bytes]]) -> str:
    payload = b"".join(
        f"{hashlib.sha256(data).hexdigest().upper()}  {relative}\n".encode()
        for relative, data in rows
    )
    return hashlib.sha256(payload).hexdigest().upper()


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--archive", type=Path, required=True)
    parser.add_argument("--apply", action="store_true")
    args = parser.parse_args()

    result = verify_archive(args.archive.resolve())
    remover = load(BASE_SEALER, "c6d_next_real_slice_notice_remover")
    contract = load(CONTRACT_PATH, "c6d_next_real_slice_seal_contract")
    original_rows = [
        (relative, require_clean_exact(result, relative))
        for relative in paths(contract)
    ]
    notice_count = sum(
        data.count(b"PRE-VALIDATION:") for _, data in original_rows
    )
    if notice_count != 6:
        raise RuntimeError(
            f"C6D_NEXT_REAL_SLICE_SEAL_NOTICE_COUNT_MISMATCH={notice_count}:6"
        )
    rows: list[tuple[str, bytes]] = []
    unmarked: list[str] = []
    for relative, data in original_rows:
        count = data.count(b"PRE-VALIDATION:")
        if count == 0:
            unmarked.append(relative)
            sealed = data
        elif count == 1:
            sealed = remover.remove_prevalidation_block(data, relative)
        else:
            raise RuntimeError(
                f"C6D_NEXT_REAL_SLICE_SEAL_PER_FILE_NOTICE_COUNT={relative}:{count}"
            )
        rows.append((relative, sealed))
    if unmarked:
        raise RuntimeError(
            "C6D_NEXT_REAL_SLICE_SEAL_UNMARKED_SCOPE=" + ",".join(unmarked)
        )
    manifest_sha = digest(rows)
    if not args.apply:
        print(
            "C6D_NEXT_REAL_SLICE_SEAL_PREVIEW_OK "
            f"files=6 notices={notice_count} source_sha={result['source_sha']} "
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
                raise RuntimeError(f"C6D_NEXT_REAL_SLICE_PREVALIDATION_REMAINS={relative}")
        actual = digest(
            [(relative, (ROOT / relative).read_bytes()) for relative, _ in rows]
        )
        if actual != manifest_sha:
            raise RuntimeError(
                f"C6D_NEXT_REAL_SLICE_SEAL_POSTWRITE_MISMATCH={actual}"
            )
    except Exception:
        for relative in reversed(written):
            (ROOT / relative).write_bytes(originals[relative])
        raise

    print(
        "C6D_NEXT_REAL_SLICE_SEAL_APPLY_OK "
        f"files=6 notices={notice_count} source_sha={result['source_sha']} "
        f"manifest_sha256={manifest_sha}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
