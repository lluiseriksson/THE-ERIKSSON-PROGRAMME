#!/usr/bin/env python3
"""Validate executable adversarial-audit manifests for SU2, CONT-C0, CONT-C1.

This is a structural judge, not a theorem prover. It prevents a verdict from
being promoted without the evidence, witness, dependency tables, and immutable
identifiers fixed by BLIND-AUDIT-PROTOCOL.md.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import subprocess
import sys
from pathlib import Path
from typing import Any


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
HEX40 = re.compile(r"^[0-9a-f]{40}$")
SHA256 = re.compile(r"^[0-9a-fA-F]{64}$")
UTC_TIMESTAMP = re.compile(
    r"^\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2}(?:\.\d+)?Z$"
)
VERDICTS = {"PASS", "FAIL", "BLOCKED"}
CORE_BASELINE_SHA = "7460e035"
CORE_BASELINE_JOBS = 8463

REQUIRED_CHECKS = {
    "SU2": [
        "SU2-1-GEOMETRY",
        "SU2-2-SPLITTING",
        "SU2-2G-GLUING",
        "SU2-3-HAAR",
        "SU2-3-CHARACTERS",
        "SU2-4-CONJUGATION",
        "SU2-4-COMPLEX-PSD",
        "SU2-5-COEFFICIENTS",
        "SU2-5-BOUNDARY-COUNT",
        "SU2-HOUSE-PROSE",
        "SU2-HOUSE-CORE",
    ],
    "CONT-C0": [
        "CONT-C0-1-REGULATORS",
        "CONT-C0-1-LIMIT-ORDER",
        "CONT-C0-2-NONARBITRARY",
        "CONT-C0-2-NONCIRCULAR",
        "CONT-C0-3-TOPOLOGY",
        "CONT-C0-3-TIGHTNESS",
        "CONT-C0-3-SUBSEQUENCE",
        "CONT-C0-3-UNIQUENESS",
        "CONT-C0-4-SCALE",
        "CONT-C0-4-RENORMALISATION",
        "CONT-C0-4-NONTRIVIALITY",
        "CONT-C0-HOUSE-PROSE",
        "CONT-C0-HOUSE-CORE",
    ],
    "CONT-C1": [
        "CONT-C1-1-DEPENDENCY-TABLE",
        "CONT-C1-1-VALIDITY-DOMAIN",
        "CONT-C1-2-UNITS",
        "CONT-C1-2-A-SCALING",
        "CONT-C1-3-VOLUME-UNIFORMITY",
        "CONT-C1-3-CUTOFF-UNIFORMITY",
        "CONT-C1-3-LIMIT-ORDER",
        "CONT-C1-4-CIRCULARITY",
        "CONT-C1-4-PHYSICAL-GAP",
        "CONT-C1-HOUSE-PROSE",
        "CONT-C1-HOUSE-CORE",
    ],
}

DEPENDENCY_KEYS = [
    "lattice_spacing_a",
    "lattice_extent",
    "physical_volume",
    "uv_cutoff",
    "ir_regulator",
    "bare_coupling",
    "renormalised_coupling",
    "observable_support",
    "renormalisation_scale",
]


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def run_git(*args: str) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        ["git", *args],
        cwd=ROOT,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
    )


def require_text(errors: list[str], obj: dict[str, Any], field: str, label: str) -> None:
    value = obj.get(field)
    if not isinstance(value, str) or not value.strip():
        errors.append(f"{label}.{field}: non-empty string required")


def validate_evidence(
    errors: list[str], check_id: str, evidence: Any, verify_files: bool
) -> None:
    if not isinstance(evidence, list):
        errors.append(f"{check_id}.evidence: list required")
        return
    for index, item in enumerate(evidence, 1):
        label = f"{check_id}.evidence[{index}]"
        if not isinstance(item, dict):
            errors.append(f"{label}: object required")
            continue
        if item.get("kind") not in {
            "file",
            "theorem",
            "command",
            "source",
            "derivation",
            "hash",
        }:
            errors.append(f"{label}.kind: unsupported evidence kind")
        require_text(errors, item, "locator", label)
        path_value = item.get("path")
        expected = item.get("sha256")
        if path_value is not None:
            if not isinstance(path_value, str) or not path_value:
                errors.append(f"{label}.path: non-empty string required")
                continue
            candidate = (ROOT / path_value).resolve()
            try:
                candidate.relative_to(ROOT)
            except ValueError:
                errors.append(f"{label}.path: escapes repository")
                continue
            if verify_files:
                if not candidate.is_file():
                    errors.append(f"{label}.path: file not found: {path_value}")
                elif expected is not None:
                    if not isinstance(expected, str) or not SHA256.fullmatch(expected):
                        errors.append(f"{label}.sha256: 64 hex characters required")
                    elif sha256_file(candidate).lower() != expected.lower():
                        errors.append(f"{label}.sha256: mismatch for {path_value}")
        elif expected is not None:
            errors.append(f"{label}.sha256: cannot be supplied without path")


def validate_checks(
    data: dict[str, Any], lane: str, errors: list[str], verify_files: bool
) -> dict[str, int]:
    raw_checks = data.get("checks")
    if not isinstance(raw_checks, list):
        errors.append("checks: list required")
        return {verdict: 0 for verdict in VERDICTS}

    by_id: dict[str, dict[str, Any]] = {}
    counts = {verdict: 0 for verdict in VERDICTS}
    for index, check in enumerate(raw_checks, 1):
        label = f"checks[{index}]"
        if not isinstance(check, dict):
            errors.append(f"{label}: object required")
            continue
        check_id = check.get("id")
        if not isinstance(check_id, str) or not check_id:
            errors.append(f"{label}.id: non-empty string required")
            continue
        if check_id in by_id:
            errors.append(f"{label}.id: duplicate {check_id}")
        by_id[check_id] = check
        verdict = check.get("verdict")
        if verdict not in VERDICTS:
            errors.append(f"{check_id}.verdict: PASS, FAIL, or BLOCKED required")
            continue
        counts[verdict] += 1
        require_text(errors, check, "criterion", check_id)
        validate_evidence(errors, check_id, check.get("evidence", []), verify_files)
        if verdict == "PASS" and not check.get("evidence"):
            errors.append(f"{check_id}: PASS requires evidence")
        if verdict == "FAIL":
            witness = check.get("witness")
            if not isinstance(witness, list) or not witness:
                errors.append(f"{check_id}: FAIL requires a non-empty witness list")
        if verdict == "BLOCKED":
            missing = check.get("missing_data")
            if not isinstance(missing, list) or not missing:
                errors.append(f"{check_id}: BLOCKED requires missing_data")

    required = REQUIRED_CHECKS[lane]
    for check_id in required:
        if check_id not in by_id:
            errors.append(f"checks: required check missing: {check_id}")
    extras = sorted(set(by_id) - set(required))
    if extras:
        errors.append(f"checks: unregistered check ids: {', '.join(extras)}")
    return counts


def validate_su2(data: dict[str, Any], errors: list[str], has_pass: bool) -> None:
    if not has_pass:
        return
    normalisations = data.get("normalisations")
    if not isinstance(normalisations, dict):
        errors.append("normalisations: object required when SU2 has PASS claims")
    else:
        for field in [
            "haar_total_mass",
            "matrix_coefficient_orthogonality",
            "character_orthogonality",
            "trace_convention",
            "wilson_action_convention",
            "coupling_convention",
        ]:
            require_text(errors, normalisations, field, "normalisations")
    reflection = data.get("reflection")
    if not isinstance(reflection, dict):
        errors.append("reflection: object required when SU2 has PASS claims")
    else:
        for field in [
            "link_map",
            "orientation_reversal",
            "path_order_reversal",
            "group_inverse_or_adjoint",
            "antilinear_extension",
            "boundary_convention",
        ]:
            require_text(errors, reflection, field, "reflection")
    gluing = data.get("gluing")
    if not isinstance(gluing, dict):
        errors.append("gluing: object required when SU2 has PASS claims")
    else:
        for field in [
            "full_configuration_map",
            "inverse_map",
            "boundary_identification",
            "product_haar_identity",
            "weight_factorisation",
        ]:
            require_text(errors, gluing, field, "gluing")


def validate_cont_c0(data: dict[str, Any], errors: list[str], has_pass: bool) -> None:
    if not has_pass:
        return
    family = data.get("regulator_family")
    if not isinstance(family, dict):
        errors.append("regulator_family: object required when CONT-C0 has PASS claims")
        return
    for field in [
        "lattice_spacing",
        "physical_volume",
        "boundary_conditions",
        "bare_parameters",
        "renormalised_parameters",
        "observables",
        "directed_limit",
        "topology",
    ]:
        require_text(errors, family, field, "regulator_family")
    for field in ["tightness_argument", "uniqueness_argument", "nontriviality_test"]:
        require_text(errors, data, field, "CONT-C0")


def validate_cont_c1(data: dict[str, Any], errors: list[str], has_pass: bool) -> None:
    if not has_pass:
        return
    constants = data.get("constants")
    if not isinstance(constants, list) or not constants:
        errors.append("constants: non-empty list required when CONT-C1 has PASS claims")
        return
    for index, constant in enumerate(constants, 1):
        label = f"constants[{index}]"
        if not isinstance(constant, dict):
            errors.append(f"{label}: object required")
            continue
        for field in ["name", "definition", "units", "validity_domain", "source_locator"]:
            require_text(errors, constant, field, label)
        dependencies = constant.get("depends_on")
        if not isinstance(dependencies, dict):
            errors.append(f"{label}.depends_on: object required")
            continue
        for key in DEPENDENCY_KEYS:
            value = dependencies.get(key)
            if value not in {"yes", "no"}:
                errors.append(f"{label}.depends_on.{key}: explicit yes/no required")
        uniform_in = constant.get("uniform_in")
        if not isinstance(uniform_in, list):
            errors.append(f"{label}.uniform_in: list required")


def validate_core_gate(data: dict[str, Any], errors: list[str]) -> None:
    gate = data.get("core_integration")
    if not isinstance(gate, dict):
        errors.append("core_integration: object required")
        return
    status = gate.get("status")
    if status not in {"not_applicable", "pending", "integrated"}:
        errors.append("core_integration.status: not_applicable, pending, or integrated required")
    if gate.get("baseline_sha") != CORE_BASELINE_SHA:
        errors.append(f"core_integration.baseline_sha: must be {CORE_BASELINE_SHA}")
    if gate.get("baseline_jobs") != CORE_BASELINE_JOBS:
        errors.append(f"core_integration.baseline_jobs: must be {CORE_BASELINE_JOBS}")
    if status == "integrated":
        observed = gate.get("observed_jobs")
        if not isinstance(observed, int) or observed <= CORE_BASELINE_JOBS:
            errors.append(
                f"core integration requires observed_jobs > {CORE_BASELINE_JOBS}"
            )
        require_text(errors, gate, "command_transcript", "core_integration")


def validate_snapshot(data: dict[str, Any], errors: list[str]) -> None:
    """Schema v2 makes the per-report snapshot and freshness seal executable."""
    main_sha = data.get("observed_main_sha")
    observed_at = data.get("observed_at_utc")
    if not isinstance(main_sha, str) or not HEX40.fullmatch(main_sha):
        errors.append("observed_main_sha: full 40-character lowercase SHA required")
    if not isinstance(observed_at, str) or not UTC_TIMESTAMP.fullmatch(observed_at):
        errors.append("observed_at_utc: ISO-8601 UTC timestamp ending in Z required")

    seal = data.get("freshness_check")
    if not isinstance(seal, dict):
        errors.append("freshness_check: object required")
        return
    status = seal.get("status")
    if status not in {"stable", "obsolete"}:
        errors.append("freshness_check.status: stable or obsolete required")
    checked_at = seal.get("checked_at_utc")
    if not isinstance(checked_at, str) or not UTC_TIMESTAMP.fullmatch(checked_at):
        errors.append(
            "freshness_check.checked_at_utc: ISO-8601 UTC timestamp ending in Z required"
        )
    current_producer = seal.get("producer_sha")
    current_main = seal.get("observed_main_sha")
    if not isinstance(current_producer, str) or not HEX40.fullmatch(current_producer):
        errors.append(
            "freshness_check.producer_sha: full 40-character lowercase SHA required"
        )
    if not isinstance(current_main, str) or not HEX40.fullmatch(current_main):
        errors.append(
            "freshness_check.observed_main_sha: full 40-character lowercase SHA required"
        )
    if status == "stable" and current_producer != data.get("producer_sha"):
        errors.append(
            "freshness_check: stable seal producer SHA must equal producer_sha"
        )
    if status == "obsolete":
        changed = seal.get("changed_files")
        if not isinstance(changed, list) or not changed:
            errors.append(
                "freshness_check: obsolete seal requires non-empty changed_files"
            )


def validate_manifest(path: Path, verify_files: bool, verify_ref: bool) -> tuple[list[str], dict[str, int]]:
    errors: list[str] = []
    try:
        data = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        return [f"cannot read manifest: {exc}"], {verdict: 0 for verdict in VERDICTS}
    if not isinstance(data, dict):
        return ["manifest root must be an object"], {verdict: 0 for verdict in VERDICTS}

    schema_version = data.get("schema_version")
    if schema_version not in {1, 2}:
        errors.append("schema_version: expected 1 or 2")
    lane = data.get("lane")
    if lane not in REQUIRED_CHECKS:
        errors.append("lane: SU2, CONT-C0, or CONT-C1 required")
        return errors, {verdict: 0 for verdict in VERDICTS}
    base_sha = data.get("audit_base_sha")
    if not isinstance(base_sha, str) or not HEX40.fullmatch(base_sha):
        errors.append("audit_base_sha: full 40-character lowercase SHA required")

    producer_ref = data.get("producer_ref")
    producer_sha = data.get("producer_sha")
    if producer_ref is None or producer_sha is None:
        if producer_ref is not None or producer_sha is not None:
            errors.append("producer_ref and producer_sha must both be null or both be set")
    else:
        if not isinstance(producer_ref, str) or not producer_ref:
            errors.append("producer_ref: non-empty string required")
        if not isinstance(producer_sha, str) or not HEX40.fullmatch(producer_sha):
            errors.append("producer_sha: full 40-character lowercase SHA required")
        elif verify_ref:
            resolved = run_git("rev-parse", producer_ref)
            if resolved.returncode != 0:
                errors.append(f"producer_ref: cannot resolve {producer_ref}")
            elif resolved.stdout.strip() != producer_sha:
                errors.append(
                    f"producer_ref: resolves to {resolved.stdout.strip()}, expected {producer_sha}"
                )
    if schema_version == 2:
        validate_snapshot(data, errors)

    counts = validate_checks(data, lane, errors, verify_files)
    has_pass = counts["PASS"] > 0
    if producer_ref is None and has_pass:
        errors.append("no producer ref/SHA: no claim may be PASS")
    validate_core_gate(data, errors)
    if lane == "SU2":
        validate_su2(data, errors, has_pass)
    elif lane == "CONT-C0":
        validate_cont_c0(data, errors, has_pass)
    else:
        validate_cont_c1(data, errors, has_pass)
    return errors, counts


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("manifests", nargs="+", type=Path)
    parser.add_argument("--no-file-hash-check", action="store_true")
    parser.add_argument("--verify-ref", action="store_true")
    parser.add_argument("--json", action="store_true")
    args = parser.parse_args()

    results = []
    failed = False
    for manifest in args.manifests:
        path = manifest if manifest.is_absolute() else (ROOT / manifest)
        errors, counts = validate_manifest(
            path, not args.no_file_hash_check, args.verify_ref
        )
        failed |= bool(errors)
        result = {
            "manifest": str(path.relative_to(ROOT) if path.is_relative_to(ROOT) else path),
            "structural_status": "FAIL" if errors else "PASS",
            "verdict_counts": counts,
            "errors": errors,
        }
        results.append(result)

    if args.json:
        print(json.dumps(results, indent=2, sort_keys=True))
    else:
        for result in results:
            counts = result["verdict_counts"]
            print(
                f"{result['structural_status']}: {result['manifest']} "
                f"(PASS={counts['PASS']} FAIL={counts['FAIL']} "
                f"BLOCKED={counts['BLOCKED']})"
            )
            for error in result["errors"]:
                print(f"  - {error}")
    return 1 if failed else 0


if __name__ == "__main__":
    raise SystemExit(main())
