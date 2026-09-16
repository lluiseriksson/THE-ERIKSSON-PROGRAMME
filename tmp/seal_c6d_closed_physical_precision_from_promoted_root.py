#!/usr/bin/env python3
"""Seal the closed physical Eq. (3.60) pair from exact cold root evidence."""

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
VERIFIER = ROOT / "tmp" / "verify_c6d_closed_physical_precision_from_promoted_root.py"
REMOVER = ROOT / "tmp" / "seal_eq337_complex_perturbed_background_prevalidation.py"
SOURCE_SHA = "768bca00ba63e52eccacd8226cee91e6cfafd39e"
RUNNER_REV = "c6d-promoted-precision-prefix-v2"
PATHS = (
    "YangMills/RG/BalabanCMP99Eq360ComplexClosedPhysicalPrecision.lean",
    "YangMills/RG/BalabanCMP99Eq360ComplexClosedPhysicalPrecisionAudit.lean",
)


def git(*args: str) -> subprocess.CompletedProcess[bytes]:
    return subprocess.run(
        ["git", "-c", "safe.directory=*", *args],
        cwd=ROOT,
        check=False,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )


def git_blob(relative: str) -> bytes:
    child = git("cat-file", "blob", f"{SOURCE_SHA}:{relative}")
    if child.returncode != 0:
        raise RuntimeError(
            f"C6D_CLOSED_PHYSICAL_SEAL_BLOB_FAILED={relative}:"
            + child.stderr.decode(errors="replace")
        )
    return child.stdout


def load_remover():
    spec = importlib.util.spec_from_file_location("c6d_closed_physical_remover", REMOVER)
    if spec is None or spec.loader is None:
        raise RuntimeError("C6D_CLOSED_PHYSICAL_REMOVER_LOAD_FAILED")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def verify_archive(archive: Path) -> dict:
    with tempfile.TemporaryDirectory(prefix="c6d-closed-physical-seal-") as temp:
        output = Path(temp) / "verification.json"
        child = subprocess.run(
            [
                sys.executable,
                str(VERIFIER),
                "--repo",
                str(ROOT),
                "--archive",
                str(archive),
                "--source-sha",
                SOURCE_SHA,
                "--runner-rev",
                RUNNER_REV,
                "--json-out",
                str(output),
            ],
            cwd=ROOT,
            check=False,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            text=True,
        )
        if child.returncode != 0:
            raise RuntimeError("C6D_CLOSED_PHYSICAL_SEAL_VERIFY_FAILED=" + child.stdout)
        result = json.loads(output.read_text(encoding="utf-8"))
    if result.get("status") != "C6D_CLOSED_PHYSICAL_FROM_PROMOTED_ROOT_OK":
        raise RuntimeError("C6D_CLOSED_PHYSICAL_SEAL_STATUS")
    if result.get("source_sha") != SOURCE_SHA:
        raise RuntimeError("C6D_CLOSED_PHYSICAL_SEAL_SOURCE")
    if result.get("runner_revision") != RUNNER_REV:
        raise RuntimeError("C6D_CLOSED_PHYSICAL_SEAL_RUNNER")
    return result


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
    remover = load_remover()

    rows: list[tuple[str, bytes]] = []
    for relative in PATHS:
        status = git("status", "--porcelain=v1", "--", relative)
        if status.returncode != 0 or status.stdout:
            raise RuntimeError(f"C6D_CLOSED_PHYSICAL_SEAL_DIRTY={relative}")
        data = git_blob(relative)
        wanted = result["boundary_blob_sha256"].get(relative)
        if hashlib.sha256(data).hexdigest() != wanted:
            raise RuntimeError(f"C6D_CLOSED_PHYSICAL_SEAL_HASH={relative}")
        worktree = (ROOT / relative).read_bytes().replace(b"\r\n", b"\n")
        if worktree != data:
            raise RuntimeError(f"C6D_CLOSED_PHYSICAL_SEAL_WORKTREE={relative}")
        if data.count(b"PRE-VALIDATION:") != 1:
            raise RuntimeError(f"C6D_CLOSED_PHYSICAL_SEAL_NOTICE={relative}")
        sealed = remover.remove_prevalidation_block(data, relative)
        if b"PRE-VALIDATION:" in sealed:
            raise RuntimeError(f"C6D_CLOSED_PHYSICAL_SEAL_NOTICE_REMAINS={relative}")
        rows.append((relative, sealed))

    manifest = digest(rows)
    if not args.apply:
        print(
            "C6D_CLOSED_PHYSICAL_SEAL_PREVIEW_OK "
            f"files={len(rows)} source_sha={SOURCE_SHA} manifest_sha256={manifest}"
        )
        return 0

    originals = {relative: (ROOT / relative).read_bytes() for relative, _ in rows}
    written: list[str] = []
    try:
        for relative, data in rows:
            (ROOT / relative).write_bytes(data)
            written.append(relative)
        actual = digest(
            [(relative, (ROOT / relative).read_bytes()) for relative, _ in rows]
        )
        if actual != manifest:
            raise RuntimeError("C6D_CLOSED_PHYSICAL_SEAL_POSTWRITE")
    except Exception:
        for relative in reversed(written):
            (ROOT / relative).write_bytes(originals[relative])
        raise

    print(
        "C6D_CLOSED_PHYSICAL_SEAL_APPLY_OK "
        f"files={len(rows)} source_sha={SOURCE_SHA} manifest_sha256={manifest}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
