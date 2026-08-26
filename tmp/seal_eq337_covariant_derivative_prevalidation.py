#!/usr/bin/env python3
"""Seal only the two remaining Eq. (3.37) derivative source/audit pairs."""

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
CORE = "YangMillsCore.lean"
MODULES = (
    "BalabanCMP99Eq337PhysicalRealCovariantDerivative",
    "BalabanCMP99Eq337PhysicalComplexCovariantDerivative",
    "BalabanCMP99Eq337PhysicalComplexPerturbedBackground",
)


def load_base():
    spec = importlib.util.spec_from_file_location("eq337_derivative_notice_remover", BASE_SEALER)
    if spec is None or spec.loader is None:
        raise RuntimeError("EQ337_DERIVATIVE_BASE_SEALER_LOAD_FAILED")
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
            f"EQ337_DERIVATIVE_SEAL_BLOB_FAILED={relative}:"
            + child.stderr.decode(errors="replace")
        )
    return child.stdout


def paths() -> list[str]:
    rows = [
        f"YangMills/RG/{module}{suffix}.lean"
        for module in MODULES
        for suffix in ("", "Audit")
    ]
    if len(rows) != 6 or len(set(rows)) != 6:
        raise RuntimeError("EQ337_DERIVATIVE_SEAL_SCOPE_INVALID")
    return rows


def read_evidence(path: Path) -> dict:
    result = json.loads(path.read_text(encoding="utf-8"))
    if result.get("status") != "EQ337_COVARIANT_DERIVATIVE_EVIDENCE_OK":
        raise RuntimeError("EQ337_DERIVATIVE_SEAL_STATUS_MISMATCH")
    if result.get("expected_declarations") != 57:
        raise RuntimeError("EQ337_DERIVATIVE_SEAL_DECLARATIONS_MISMATCH")
    source_sha = result.get("source_sha")
    if not isinstance(source_sha, str) or re.fullmatch(r"[0-9a-f]{40}", source_sha) is None:
        raise RuntimeError("EQ337_DERIVATIVE_SEAL_SOURCE_INVALID")
    if not isinstance(result.get("boundary_blob_sha256"), dict):
        raise RuntimeError("EQ337_DERIVATIVE_SEAL_HASHES_MISSING")
    return result


def require_clean_exact(result: dict, relative: str) -> bytes:
    status = git("status", "--porcelain=v1", "--", relative)
    if status.returncode != 0 or status.stdout:
        raise RuntimeError(f"EQ337_DERIVATIVE_SEAL_DIRTY={relative}")
    data = git_blob(result["source_sha"], relative)
    wanted = result["boundary_blob_sha256"].get(relative)
    measured = hashlib.sha256(data).hexdigest()
    if measured != wanted:
        raise RuntimeError(f"EQ337_DERIVATIVE_SEAL_EVIDENCE_MISMATCH={relative}")
    if (ROOT / relative).read_bytes().replace(b"\r\n", b"\n") != data:
        raise RuntimeError(f"EQ337_DERIVATIVE_SEAL_WORKTREE_DIVERGED={relative}")
    return data


def sealed_core(data: bytes) -> bytes:
    text = data.decode("utf-8")
    imports = [f"import YangMills.RG.{module}Audit" for module in MODULES]
    present = [line for line in imports if line in text]
    if present:
        raise RuntimeError(f"EQ337_DERIVATIVE_CORE_IMPORT_ALREADY_PRESENT={present!r}")
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
    parser.add_argument("--evidence-json", type=Path, required=True)
    parser.add_argument("--apply", action="store_true")
    args = parser.parse_args()
    result = read_evidence(args.evidence_json.resolve())
    remover = load_base()
    boundary = [
        (
            relative,
            remover.remove_prevalidation_block(require_clean_exact(result, relative), relative),
        )
        for relative in paths()
    ]
    core_status = git("status", "--porcelain=v1", "--", CORE)
    if core_status.returncode != 0 or core_status.stdout:
        raise RuntimeError("EQ337_DERIVATIVE_CORE_DIRTY")
    core_blob = git_blob(result["source_sha"], CORE)
    if (ROOT / CORE).read_bytes().replace(b"\r\n", b"\n") != core_blob:
        raise RuntimeError("EQ337_DERIVATIVE_CORE_DIVERGED")
    rows = [*boundary, (CORE, sealed_core(core_blob))]
    manifest_sha = digest(rows)
    if not args.apply:
        print(
            "EQ337_COVARIANT_DERIVATIVE_SEAL_PREVIEW_OK "
            f"files=7 source_sha={result['source_sha']} manifest_sha256={manifest_sha}"
        )
        return 0

    originals = {relative: (ROOT / relative).read_bytes() for relative, _ in rows}
    written: list[str] = []
    try:
        for relative, data in rows:
            (ROOT / relative).write_bytes(data)
            written.append(relative)
        for relative, _ in boundary:
            if "PRE-VALIDATION:" in (ROOT / relative).read_text(encoding="utf-8-sig"):
                raise RuntimeError(f"EQ337_DERIVATIVE_PREVALIDATION_REMAINS={relative}")
        actual = digest([(relative, (ROOT / relative).read_bytes()) for relative, _ in rows])
        if actual != manifest_sha:
            raise RuntimeError(f"EQ337_DERIVATIVE_POSTWRITE_MISMATCH={actual}")
    except Exception:
        for relative in reversed(written):
            (ROOT / relative).write_bytes(originals[relative])
        raise
    print(
        "EQ337_COVARIANT_DERIVATIVE_SEAL_APPLY_OK "
        f"files=7 source_sha={result['source_sha']} manifest_sha256={manifest_sha}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
