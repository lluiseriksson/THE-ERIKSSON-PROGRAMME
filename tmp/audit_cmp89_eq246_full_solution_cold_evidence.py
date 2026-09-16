#!/usr/bin/env python3
"""Fail-closed verifier for the cold CMP89 Eq. (2.46) Actions artifact."""

from __future__ import annotations

import argparse
import hashlib
from pathlib import Path
import re
import tarfile


EXPECTED_SOURCE = "febce96d017f4ec8494354656f88b0dca56c1854"
EXPECTED_CONTROL = "6f1f0d646933fad80c4208868b9c926aa78f0d6f"
EXPECTED_MATHLIB = "07642720480157414db592fa85b626dafb71355b"
EXPECTED_TOOLCHAIN = (
    "bf3e0a4025e47a0bea9ed907d12dcccd3d3590b1d8ad6c55a915298b01ad9d3e"
)
EXPECTED_AXIOMS = {
    "YangMills.RG.sum_row_mul_cmp89Eq246StabilizedAliasFullSolution_eq",
    "YangMills.RG.cmp89Eq246EntireAliasPrecisionMatrix_mulVec_stabilizedFullSolution",
}
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
EXPECTED_INNER_FILES = {
    "audit.log",
    "audit.status",
    "axioms.txt",
    "cache-get.log",
    "checkpoint.txt",
    "FINAL_STATUS",
    "focal.log",
    "focal.status",
    "lake-update.log",
    "mathlib.txt",
    "SHA256SUMS",
    "toolchain.txt",
}


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def parse_assignments(text: str) -> dict[str, str]:
    result: dict[str, str] = {}
    for line in text.splitlines():
        if "=" in line:
            key, value = line.split("=", 1)
            result[key] = value
    return result


def require_stage(path: Path, stage: str) -> int:
    text = path.read_text(encoding="utf-8").strip()
    match = re.fullmatch(
        rf"stage={re.escape(stage)} exit=0 seconds=([0-9]+)", text
    )
    if match is None:
        raise RuntimeError(f"INVALID_STAGE_STATUS path={path} text={text!r}")
    return int(match.group(1))


def verify_axioms(path: Path) -> None:
    lines = [line for line in path.read_text(encoding="utf-8").splitlines() if line]
    if len(lines) != len(EXPECTED_AXIOMS):
        raise RuntimeError(f"AXIOM_LINE_COUNT_MISMATCH={len(lines)}")
    names: set[str] = set()
    for line in lines:
        if "=" not in line:
            raise RuntimeError(f"INVALID_AXIOM_LINE={line!r}")
        name, raw = line.split("=", 1)
        names.add(name)
        axioms = {item for item in raw.split(",") if item}
        unexpected = axioms - ALLOWED_AXIOMS
        if unexpected:
            raise RuntimeError(f"UNEXPECTED_AXIOMS {name} {sorted(unexpected)}")
    if names != EXPECTED_AXIOMS:
        raise RuntimeError(f"AXIOM_DECLARATION_MISMATCH={sorted(names)}")


def verify_manifest(evidence: Path) -> int:
    lines = [
        line for line in (evidence / "SHA256SUMS").read_text(encoding="utf-8").splitlines()
        if line
    ]
    recorded: dict[str, str] = {}
    for line in lines:
        match = re.fullmatch(r"([0-9a-f]{64})  evidence/(.+)", line)
        if match is None:
            raise RuntimeError(f"INVALID_MANIFEST_LINE={line!r}")
        digest, name = match.groups()
        if name in recorded:
            raise RuntimeError(f"DUPLICATE_MANIFEST_ENTRY={name}")
        recorded[name] = digest
    expected = EXPECTED_INNER_FILES - {"SHA256SUMS"}
    if set(recorded) != expected:
        raise RuntimeError(
            f"MANIFEST_SCOPE_MISMATCH expected={sorted(expected)} actual={sorted(recorded)}"
        )
    for name, digest in recorded.items():
        measured = sha256(evidence / name)
        if measured != digest:
            raise RuntimeError(
                f"MANIFEST_HASH_MISMATCH file={name} expected={digest} actual={measured}"
            )
    return len(recorded)


def verify_inner_archive(archive: Path, evidence: Path) -> int:
    with tarfile.open(archive, mode="r:gz") as bundle:
        members = bundle.getmembers()
        names = [member.name.rstrip("/") for member in members if member.isfile()]
        expected = {f"evidence/{name}" for name in EXPECTED_INNER_FILES}
        if set(names) != expected:
            raise RuntimeError(
                f"INNER_ARCHIVE_SCOPE_MISMATCH expected={sorted(expected)} actual={sorted(names)}"
            )
        for member in members:
            if member.name.startswith("/") or ".." in Path(member.name).parts:
                raise RuntimeError(f"UNSAFE_INNER_MEMBER={member.name}")
            if not member.isfile():
                continue
            stream = bundle.extractfile(member)
            if stream is None:
                raise RuntimeError(f"INNER_MEMBER_UNREADABLE={member.name}")
            archived = hashlib.sha256(stream.read()).hexdigest()
            local = sha256(evidence / Path(member.name).name)
            if archived != local:
                raise RuntimeError(
                    f"INNER_MEMBER_HASH_MISMATCH={member.name} archived={archived} local={local}"
                )
    return len(members)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--artifact-root", type=Path, required=True)
    parser.add_argument("--outer-zip", type=Path, required=True)
    args = parser.parse_args()

    root = args.artifact_root.resolve()
    evidence = root / "evidence"
    archive = root / "cmp89-eq246-full-solution-evidence.tar.gz"
    if not evidence.is_dir():
        raise RuntimeError(f"EVIDENCE_DIRECTORY_MISSING={evidence}")
    if not archive.is_file():
        raise RuntimeError(f"INNER_ARCHIVE_MISSING={archive}")
    if not args.outer_zip.is_file():
        raise RuntimeError(f"OUTER_ZIP_MISSING={args.outer_zip}")

    actual_files = {path.name for path in evidence.iterdir() if path.is_file()}
    expected_outer_files = EXPECTED_INNER_FILES | {"ARCHIVE_SHA256"}
    if actual_files != expected_outer_files:
        raise RuntimeError(
            f"EVIDENCE_SCOPE_MISMATCH expected={sorted(expected_outer_files)} actual={sorted(actual_files)}"
        )

    checkpoint = parse_assignments((evidence / "checkpoint.txt").read_text(encoding="utf-8"))
    expected_checkpoint = {
        "SOURCE_SHA": EXPECTED_SOURCE,
        "ACTUAL_SOURCE_HEAD": EXPECTED_SOURCE,
        "CONTROL_SHA": EXPECTED_CONTROL,
        "GITHUB_SHA": EXPECTED_CONTROL,
        "COLD_MODE": "true",
    }
    for key, value in expected_checkpoint.items():
        if checkpoint.get(key) != value:
            raise RuntimeError(
                f"CHECKPOINT_MISMATCH key={key} expected={value} actual={checkpoint.get(key)}"
            )

    mathlib = parse_assignments((evidence / "mathlib.txt").read_text(encoding="utf-8"))
    if mathlib.get("MATHLIB_SHA") != EXPECTED_MATHLIB:
        raise RuntimeError(f"MATHLIB_MISMATCH={mathlib.get('MATHLIB_SHA')}")
    toolchain = parse_assignments((evidence / "toolchain.txt").read_text(encoding="utf-8"))
    if toolchain.get("TOOLCHAIN_ASSET_SHA256") != EXPECTED_TOOLCHAIN:
        raise RuntimeError(
            f"TOOLCHAIN_MISMATCH={toolchain.get('TOOLCHAIN_ASSET_SHA256')}"
        )
    if (evidence / "FINAL_STATUS").read_text(encoding="utf-8").strip() != "FINAL_STATUS=PASS":
        raise RuntimeError("FINAL_STATUS_NOT_PASS")

    focal_seconds = require_stage(evidence / "focal.status", "eq246_full_solution_focal")
    audit_seconds = require_stage(evidence / "audit.status", "eq246_full_solution_audit")
    verify_axioms(evidence / "axioms.txt")
    manifest_entries = verify_manifest(evidence)

    archive_hash = sha256(archive)
    archive_record = (evidence / "ARCHIVE_SHA256").read_text(encoding="utf-8").strip()
    if archive_record != f"{archive_hash}  cmp89-eq246-full-solution-evidence.tar.gz":
        raise RuntimeError(
            f"ARCHIVE_HASH_RECORD_MISMATCH expected={archive_hash} actual={archive_record!r}"
        )
    inner_members = verify_inner_archive(archive, evidence)
    outer_hash = sha256(args.outer_zip)

    print("CMP89_EQ246_FULL_SOLUTION_COLD_EVIDENCE_OK")
    print(f"SOURCE_SHA={EXPECTED_SOURCE}")
    print(f"CONTROL_SHA={EXPECTED_CONTROL}")
    print(f"FOCAL_SECONDS={focal_seconds}")
    print(f"AUDIT_SECONDS={audit_seconds}")
    print(f"MANIFEST_ENTRIES={manifest_entries}")
    print(f"INNER_MEMBERS={inner_members}")
    print(f"INNER_ARCHIVE_SHA256={archive_hash.upper()}")
    print(f"OUTER_ARTIFACT_ZIP_SHA256={outer_hash.upper()}")


if __name__ == "__main__":
    main()
