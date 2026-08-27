#!/usr/bin/env python3
"""Verify and preserve one executed Eq. (3.51) sign-no-go Colab gate."""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re
import shutil
import subprocess
import tarfile
import tempfile


ROOT = Path(__file__).resolve().parents[1]
SOURCE_SHA = "c1e3814bb70036a6d6b61f39e517aab017043a50"
RUNNER_REV = "cmp99-eq351-diagonal-sign-nogo-v4"
MATHLIB_SHA = "07642720480157414db592fa85b626dafb71355b"
ASSET_SHA = "bf3e0a4025e47a0bea9ed907d12dcccd3d3590b1d8ad6c55a915298b01ad9d3e"
SOURCE_PATHS = (
    "YangMills/RG/BalabanCMP99Eq351DiagonalSignNoGo.lean",
    "YangMills/RG/BalabanCMP99Eq351DiagonalSignNoGoAudit.lean",
    "tmp/CMP99-EQ351-DIAGONAL-SIGN-NOGO-PREVALIDATION-PATHS.txt",
)


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest().upper()


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest().upper()


def notebook_transcript(path: Path) -> str:
    notebook = json.loads(path.read_text(encoding="utf-8"))
    chunks: list[str] = []
    for cell in notebook.get("cells", []):
        for output in cell.get("outputs", []):
            text = output.get("text", "")
            chunks.extend(text if isinstance(text, list) else [str(text)])
    return "".join(chunks)


def exact_marker(text: str, name: str, pattern: str) -> str:
    values = re.findall(rf"(?m)^{re.escape(name)}=({pattern})\s*$", text)
    if len(values) != 1:
        raise RuntimeError(f"EQ351_SIGN_NOGO_MARKER_COUNT={name}:{len(values)} WANT=1")
    return values[0]


def git_blob(commit: str, path: str) -> bytes:
    return subprocess.check_output(
        ["git", "cat-file", "blob", f"{commit}:{path}"], cwd=ROOT
    )


def safe_extract(archive_path: Path, destination: Path) -> None:
    with tarfile.open(archive_path, "r:gz") as archive:
        unsafe = [
            member.name
            for member in archive.getmembers()
            if member.issym()
            or member.islnk()
            or Path(member.name).is_absolute()
            or ".." in Path(member.name).parts
        ]
        if unsafe:
            raise RuntimeError(f"EQ351_SIGN_NOGO_UNSAFE_ARCHIVE={unsafe!r}")
        archive.extractall(destination, filter="data")


def audit_axioms(text: str) -> list[list[str]]:
    clean = re.sub(r"\x1b\[[0-9;]*m", "", text).replace("\r", "")
    compact = "".join(clean.split())
    blocks = re.findall(r"dependsonaxioms:(\[[^\]]*\])", compact)
    if compact.count("dependsonaxioms:") != 3 or len(blocks) != 3:
        raise RuntimeError("EQ351_SIGN_NOGO_AUDIT_COUNT_MISMATCH")
    forbidden = ("sorryAx", "Lean.ofReduceBool", "ofReduceBool")
    if any(name in compact for name in forbidden):
        raise RuntimeError("EQ351_SIGN_NOGO_FORBIDDEN_AXIOM")
    allowed = {"propext", "Classical.choice", "Quot.sound"}
    parsed: list[list[str]] = []
    for block in blocks:
        names = sorted(
            name.strip()
            for name in block.removeprefix("[").removesuffix("]").split(",")
            if name.strip()
        )
        if not set(names).issubset(allowed):
            raise RuntimeError(f"EQ351_SIGN_NOGO_UNEXPECTED_AXIOMS={names!r}")
        parsed.append(names)
    return parsed


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--notebook", type=Path, required=True)
    parser.add_argument("--archive", type=Path, required=True)
    parser.add_argument("--destination", type=Path, required=True)
    args = parser.parse_args()

    notebook = args.notebook.resolve()
    archive = args.archive.resolve()
    destination = args.destination.resolve()
    if not notebook.is_file() or not archive.is_file():
        raise RuntimeError("EQ351_SIGN_NOGO_INPUT_MISSING")
    if destination.exists():
        raise RuntimeError(f"EQ351_SIGN_NOGO_DESTINATION_EXISTS={destination}")
    text = notebook_transcript(notebook)
    if exact_marker(text, "FINAL_STATUS", r"(?:PASS|FAIL).*").split()[0] != "PASS":
        raise RuntimeError("EQ351_SIGN_NOGO_FINAL_STATUS_NOT_PASS")
    if exact_marker(text, "RUNNER_REV", r"[^\s]+.*").split()[0] != RUNNER_REV:
        raise RuntimeError("EQ351_SIGN_NOGO_RUNNER_REV_MISMATCH")
    if exact_marker(text, "TOOLCHAIN_ASSET_SHA256", r"[A-Fa-f0-9]{64}").upper() != ASSET_SHA.upper():
        raise RuntimeError("EQ351_SIGN_NOGO_TOOLCHAIN_HASH_MISMATCH")
    archive_marker = exact_marker(text, "EVIDENCE_SHA256", r"[A-Fa-f0-9]{64}").upper()
    if sha256(archive) != archive_marker:
        raise RuntimeError("EQ351_SIGN_NOGO_ARCHIVE_HASH_MISMATCH")

    destination.parent.mkdir(parents=True, exist_ok=True)
    staging = Path(tempfile.mkdtemp(prefix=".eq351-sign-nogo-", dir=destination.parent))
    try:
        copied_notebook = staging / "executed-eq351-diagonal-sign-nogo.ipynb"
        copied_archive = staging / archive.name
        extracted = staging / "extracted"
        extracted.mkdir()
        shutil.copyfile(notebook, copied_notebook)
        shutil.copyfile(archive, copied_archive)
        safe_extract(copied_archive, extracted)
        roots = [path for path in extracted.iterdir() if path.is_dir()]
        if len(roots) != 1:
            raise RuntimeError(f"EQ351_SIGN_NOGO_ARCHIVE_ROOTS={len(roots)} WANT=1")
        evidence = roots[0]
        result = json.loads((evidence / "result.json").read_text(encoding="utf-8"))
        if result != {
            "runner_rev": RUNNER_REV,
            "source_sha": SOURCE_SHA,
            "status": "PASS",
            "stage": "audit",
            "seconds": result.get("seconds"),
        }:
            raise RuntimeError(f"EQ351_SIGN_NOGO_RESULT_MISMATCH={result!r}")
        if not isinstance(result.get("seconds"), (int, float)) or result["seconds"] <= 0:
            raise RuntimeError("EQ351_SIGN_NOGO_RESULT_SECONDS_INVALID")
        source_hashes = json.loads((evidence / "source-hashes.json").read_text(encoding="utf-8"))
        expected_hashes = {
            path: hashlib.sha256(git_blob(SOURCE_SHA, path)).hexdigest()
            for path in SOURCE_PATHS
        }
        if source_hashes != expected_hashes:
            raise RuntimeError("EQ351_SIGN_NOGO_SOURCE_HASHES_MISMATCH")
        if (evidence / "mathlib_head.log").read_text(encoding="utf-8").strip() != MATHLIB_SHA:
            raise RuntimeError("EQ351_SIGN_NOGO_MATHLIB_PIN_MISMATCH")
        focal = (evidence / "focal.log").read_text(encoding="utf-8")
        if "Build completed successfully" not in focal:
            raise RuntimeError("EQ351_SIGN_NOGO_FOCAL_SUCCESS_MISSING")
        axioms = audit_axioms((evidence / "audit.log").read_text(encoding="utf-8"))
        manifest = {
            "status": "EQ351_DIAGONAL_SIGN_NOGO_EVIDENCE_PACKAGE_OK",
            "source_sha": SOURCE_SHA,
            "runner_rev": RUNNER_REV,
            "axiom_blocks": axioms,
            "source_blob_sha256": {path: value.upper() for path, value in expected_hashes.items()},
            "files": {
                copied_notebook.name: sha256(copied_notebook),
                copied_archive.name: sha256(copied_archive),
            },
        }
        (staging / "manifest.json").write_text(
            json.dumps(manifest, indent=2, sort_keys=True) + "\n", encoding="utf-8", newline="\n"
        )
        (staging / "SHA256SUMS").write_text(
            "".join(
                f"{sha256(path)}  {path.name}\n"
                for path in sorted(staging.iterdir(), key=lambda item: item.name)
                if path.is_file() and path.name != "SHA256SUMS"
            ),
            encoding="utf-8",
            newline="\n",
        )
        staging.replace(destination)
    except Exception:
        shutil.rmtree(staging, ignore_errors=True)
        raise

    print(
        "EQ351_DIAGONAL_SIGN_NOGO_EVIDENCE_PACKAGE_OK "
        f"destination={destination} manifest_sha256={sha256(destination / 'manifest.json')}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
