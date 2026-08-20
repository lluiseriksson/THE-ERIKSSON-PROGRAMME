#!/usr/bin/env python3
"""Fail-closed audit for the exact P0--P9 v56 Colab evidence archive."""

from __future__ import annotations

import hashlib
import json
from pathlib import Path, PurePosixPath
import re
import tarfile


ROOT = Path(__file__).resolve().parents[1]
PATHS = ROOT / "tmp" / "P0-P9-SCRATCH-PATHS.txt"
MANIFEST = ROOT / "tmp" / "P0-P9-SCRATCH-MANIFEST.sha256"
PATHS_SHA256 = "FEC594C0FBA52E14F8CC1E1BA886202FCDF2E425DE2C93E56DBF59FEEBB2FA61"
MANIFEST_SHA256 = "BEE10E78FC49F7EAC8961D7AC7462F1200E1F3832DBCDC35DBB080483681803F"
SOURCE_SHA = "1b98e644347a96530b8f2755d67febc132cb9774"
RUNNER_REV = "p0-p9-prefix-combes-thomas-v56"
MATHLIB_SHA = "07642720480157414db592fa85b626dafb71355b"
EVIDENCE_ROOT = "hrpoly-p0-p9-prefix-combes-thomas-evidence"
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
AXIOM_COUNTS = {
    "tmp/P0CanonicalPrefixTowerAudit.lean": 10,
    "tmp/P1CoefficientMonotonicityAudit.lean": 8,
    "tmp/P2SourceCoefficientCoercivityAudit.lean": 26,
    "tmp/P2bEffectiveQuadraticAudit.lean": 10,
    "tmp/P2cCoarseCovarianceAudit.lean": 24,
    "tmp/P3ScalarRecurrenceAudit.lean": 9,
    "tmp/P3BlockGaussianAlgebraAudit.lean": 2,
    "tmp/P3TypedSchurBracketsAudit.lean": 8,
    "tmp/P3TypedGreenInverseAudit.lean": 8,
    "tmp/P3SourceStepCoisometryAudit.lean": 2,
    "tmp/P3PhysicalScalarSpecializationAudit.lean": 4,
    "tmp/P3PhysicalOperatorDictionaryAudit.lean": 3,
    "tmp/P3PhysicalGreenRecurrenceAudit.lean": 3,
    "tmp/P3PhysicalGreenRecurrenceAggregateAudit.lean": 18,
    "tmp/P4aPhysicalBaseAudit.lean": 12,
    "tmp/P4bFiniteTelescopingAudit.lean": 14,
    "tmp/P5PhysicalGreenScaleDictionaryAudit.lean": 13,
    "tmp/P7SourceSeparatedAmbientPrefixPrecisionAudit.lean": 8,
    "tmp/P8SourceSeparatedRegionalPrefixGreenAudit.lean": 5,
    "tmp/P9SourceSeparatedPrefixCombesThomasAudit.lean": 12,
}
BASE_NO_APT = (
    "download_toolchain",
    "extract_toolchain",
    "lean_version",
    "lake_version",
    "clone",
    "checkout",
    "head",
    "overlay_text_guard",
    "import_prefix_guard",
    "lake_update",
    "mathlib_pin",
    "cache_get",
)
BASE_WITH_APT = (
    "download_toolchain",
    "apt_update",
    "install_zstd",
    *BASE_NO_APT[1:],
)
QUEUE_PREFIX = (
    "p0_p9_static_gate",
    "p0_p9_static_selftest",
    "p0_p9_p2b_algebra_repro",
    "p0_p9_p3_algebra_repro",
    "p0_p9_p3_typed_averaging_repro",
    "p0_p9_p3_typed_green_inverse_repro",
    "p0_p9_p3_physical_dictionary_repro",
    "p0_p9_materialize_project_prerequisites",
    "p0_p9_prepare_scratch_build_dir",
)


def sha256(payload: bytes) -> str:
    return hashlib.sha256(payload).hexdigest()


def exact_paths() -> list[str]:
    if sha256(PATHS.read_bytes()).upper() != PATHS_SHA256:
        raise ValueError("P0--P9 path-list digest drift")
    if sha256(MANIFEST.read_bytes()).upper() != MANIFEST_SHA256:
        raise ValueError("P0--P9 manifest digest drift")
    paths = [line for line in PATHS.read_text(encoding="utf-8-sig").splitlines() if line]
    if len(paths) != 39:
        raise ValueError(f"P0--P9 path count={len(paths)}, expected=39")
    return paths


def stage_for(index: int, path: str) -> str:
    stem = Path(path).stem
    return f"p0_p9_{index:02d}_{re.sub(r'[^A-Za-z0-9]+', '_', stem).lower()}"


def exact_queue(paths: list[str]) -> tuple[str, ...]:
    result = list(QUEUE_PREFIX)
    for index, path in enumerate(paths, start=1):
        if path == "tmp/P7SourceSeparatedAmbientPrefixPrecision.lean":
            result.append("p0_p9_materialize_p7_p9_project_prerequisites")
        result.append(stage_for(index, path))
    return tuple(result)


def read_regular_members(path: Path) -> dict[str, bytes]:
    members: dict[str, bytes] = {}
    with tarfile.open(path, "r:gz") as archive:
        for member in archive.getmembers():
            name = PurePosixPath(member.name)
            if name.is_absolute() or ".." in name.parts:
                raise ValueError(f"unsafe archive path: {member.name}")
            if member.isdir():
                continue
            if not member.isfile() or member.name in members:
                raise ValueError(f"invalid archive member: {member.name}")
            stream = archive.extractfile(member)
            if stream is None:
                raise ValueError(f"unreadable archive member: {member.name}")
            members[member.name] = stream.read()
    return members


def parse_axioms(output: str, expected: int) -> int:
    compact = re.sub(r"\s+", "", output)
    for forbidden in ("sorryAx", "ofReduceBool"):
        if forbidden in compact:
            raise ValueError(f"forbidden axiom marker: {forbidden}")
    blocks = re.findall(r"dependsonaxioms:\[([^\]]*)\]", compact)
    pure = compact.count("doesnotdependonanyaxioms")
    if len(blocks) + pure != expected:
        raise ValueError(
            f"axiom header count={len(blocks) + pure}, expected={expected}"
        )
    for index, body in enumerate(blocks):
        names = {name for name in body.split(",") if name}
        if not names.issubset(ALLOWED_AXIOMS):
            raise ValueError(f"forbidden axiom block {index}: {sorted(names)}")
    return len(blocks) + pure


def audit(path: Path) -> str:
    paths = exact_paths()
    queue = exact_queue(paths)
    members = read_regular_members(path)
    evidence_name = f"{EVIDENCE_ROOT}/evidence.json"
    if evidence_name not in members:
        raise ValueError("evidence.json missing")
    evidence = json.loads(members[evidence_name].decode("utf-8"))
    if (evidence.get("source_sha"), evidence.get("runner_rev")) != (
        SOURCE_SHA,
        RUNNER_REV,
    ):
        raise ValueError("source/runner identity mismatch")
    if evidence.get("mathlib_sha") != MATHLIB_SHA:
        raise ValueError("Mathlib pin mismatch")
    if evidence.get("status") != "PASS":
        raise ValueError(f"non-PASS evidence status: {evidence.get('status')!r}")
    records = evidence.get("records")
    if not isinstance(records, list):
        raise ValueError("records list missing")
    stages = tuple(record.get("stage") for record in records)
    if stages not in (BASE_NO_APT + queue, BASE_WITH_APT + queue):
        raise ValueError(f"exact stage order mismatch: records={len(stages)}")

    expected_members = {evidence_name}
    logs: dict[str, str] = {}
    for index, record in enumerate(records):
        if not isinstance(record, dict) or record.get("exit") != 0:
            raise ValueError(f"nonzero or malformed record {index}")
        stage = record["stage"]
        log_name = record.get("log")
        digest = record.get("output_sha256")
        if not isinstance(log_name, str) or PurePosixPath(log_name).name != log_name:
            raise ValueError(f"unsafe log name: {stage}")
        member_name = f"{EVIDENCE_ROOT}/{log_name}"
        expected_members.add(member_name)
        if member_name not in members:
            raise ValueError(f"stage log missing: {stage}")
        if sha256(members[member_name]) != digest:
            raise ValueError(f"stage log hash mismatch: {stage}")
        logs[stage] = members[member_name].decode("utf-8")
    extras = sorted(set(members) - expected_members)
    if extras:
        raise ValueError(f"unexpected archive members: {extras}")

    if SOURCE_SHA not in logs["head"]:
        raise ValueError("HEAD readout mismatch")
    if MATHLIB_SHA not in logs["mathlib_pin"]:
        raise ValueError("Mathlib readout mismatch")
    if "Lean (version 4.29.0-rc6" not in logs["lean_version"]:
        raise ValueError("Lean version readout mismatch")
    if "Lake version 5.0.0" not in logs["lake_version"]:
        raise ValueError("Lake version readout mismatch")
    if "P0_P9_DIAGNOSTIC_STATIC_OK" not in logs["p0_p9_static_gate"]:
        raise ValueError("static-gate readout missing")
    if "P0_P9_DIAGNOSTIC_SELFTEST_OK" not in logs["p0_p9_static_selftest"]:
        raise ValueError("static self-test readout missing")

    total_headers = 0
    for index, source in enumerate(paths, start=1):
        expected = AXIOM_COUNTS.get(source)
        if expected is None:
            continue
        total_headers += parse_axioms(logs[stage_for(index, source)], expected)
    expected_total = sum(AXIOM_COUNTS.values())
    if total_headers != expected_total:
        raise ValueError(
            f"total axiom headers={total_headers}, expected={expected_total}"
        )
    return (
        "P0_P9_V56_EVIDENCE_OK "
        f"source_sha={SOURCE_SHA} runner_rev={RUNNER_REV} status=PASS "
        f"records={len(records)} paths={len(paths)} axiom_headers={total_headers} "
        f"archive_sha256={sha256(path.read_bytes())}"
    )


if __name__ == "__main__":
    import argparse

    parser = argparse.ArgumentParser()
    parser.add_argument("archive", type=Path)
    args = parser.parse_args()
    print(audit(args.archive.resolve()))
