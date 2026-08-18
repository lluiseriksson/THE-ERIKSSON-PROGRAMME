#!/usr/bin/env python3
"""Read-only static audit for promoting the P0--P5 scratch closure.

This is deliberately not a Lean validator.  It checks the mechanical part of
promotion before any tracked source is created: proposed module-path
collisions, provisional declaration names against existing tracked
declarations, sibling-audit coverage, and the exact linear tmp import graph.
"""

from __future__ import annotations

import hashlib
import re
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
TMP = ROOT / "tmp"

SOURCES: tuple[tuple[str, str], ...] = (
    ("P0CanonicalPrefixTower.lean", "BalabanCMP99SourceCanonicalPrefixTower.lean"),
    ("P1CoefficientMonotonicity.lean", "BalabanCMP99SourcePrefixPoincare.lean"),
    ("P2SourceCoefficientCoercivity.lean", "BalabanCMP85SourcePrefixGreen.lean"),
    ("P2bEffectiveQuadratic.lean", "BalabanCMP85Eq221EffectiveQuadratic.lean"),
    ("P2cCoarseCovariance.lean", "BalabanCMP85Eq230CoarseCovariance.lean"),
    ("P3ScalarRecurrence.lean", "BalabanCMP85ScalarRecurrence.lean"),
    ("P3BlockGaussianAlgebra.lean", "BalabanCMP85BlockGaussianAlgebra.lean"),
    ("P3TypedSchurBrackets.lean", "BalabanCMP85TypedSchurBrackets.lean"),
    ("P3TypedGreenInverse.lean", "BalabanCMP85TypedGreenInverse.lean"),
    ("P3SourceStepCoisometry.lean", "BalabanCMP85SourceStepCoisometry.lean"),
    ("P3PhysicalScalarSpecialization.lean", "BalabanCMP85PhysicalScalarSpecialization.lean"),
    ("P3PhysicalOperatorDictionary.lean", "BalabanCMP85PhysicalOperatorDictionary.lean"),
    ("P3PhysicalGreenRecurrence.lean", "BalabanCMP85Eq241Eq242PhysicalGreenRecurrence.lean"),
    ("P4aPhysicalBase.lean", "BalabanCMP85Eq230BaseCovariance.lean"),
    ("P4bFiniteTelescoping.lean", "BalabanCMP85Eq243PhysicalGreenScaleSum.lean"),
    ("P5PhysicalGreenScaleDictionary.lean", "BalabanCMP89Eq234PhysicalGreenScaleDictionary.lean"),
)
P3_AGGREGATE: tuple[str, ...] = (
    "scratch_cmp85RecurrenceBeta_mul_add_eq_mul",
    "scratch_cmp85_rightSchurBracket_eq_zero",
    "scratch_cmp85_leftSchurBracket_eq_zero",
    "scratch_cmp85TypedStepProjector_idempotent",
    "scratch_cmp85Typed_rightSchurBracket_eq_zero",
    "scratch_cmp85Typed_leftSchurBracket_eq_zero",
    "scratch_cmp85TypedGreenCandidate_rightInverse",
    "scratch_cmp85TypedGreenCandidate_leftInverse",
    "scratch_cmp85TypedGreen_eq_candidate",
    "scratch_cmp85Typed_averagedGreenRecurrence",
    "scratch_cmp85SourceWeightedAdjoint_succ",
    "scratch_cmp85SourceStep_comp_weightedAdjoint",
    "scratch_cmp85SourceGeneratedPrefixPrecision_eq_typed",
    "scratch_cmp85SourceGeneratedCoarsePrecision_eq_typed",
    "scratch_cmp85SourceGeneratedNextPrefixPrecision_eq_typed",
    "scratch_cmp85SourceGeneratedGreenRecurrence_typed",
    "scratch_cmp85SourceGeneratedGreenRecurrence_eq242",
    "scratch_cmp85SourceGeneratedGreenRecurrence_eq241",
)

DECL = re.compile(
    r"(?m)^(?:noncomputable\s+)?"
    r"(?:def|abbrev|theorem|lemma|structure|class)\s+([A-Za-z0-9_.]+)"
)
PRINT = re.compile(r"(?m)^#print axioms YangMills\.RG\.([A-Za-z0-9_.]+)")
IMPORT = re.compile(r"(?m)^import\s+([^\s]+)")


def promoted_name(name: str) -> str:
    if name.startswith("scratch_"):
        return name.removeprefix("scratch_")
    if name.startswith("Scratch"):
        return name.removeprefix("Scratch")
    return name


def main() -> int:
    failures: list[str] = []
    expected_paths = [
        path
        for scratch_name, _ in SOURCES
        for path in (f"tmp/{scratch_name}", f"tmp/{Path(scratch_name).stem}Audit.lean")
    ]
    aggregate_path = "tmp/P3PhysicalGreenRecurrenceAggregateAudit.lean"
    aggregate_index = expected_paths.index(
        "tmp/P3PhysicalGreenRecurrenceAudit.lean"
    ) + 1
    expected_paths.insert(aggregate_index, aggregate_path)
    path_list = TMP / "P0-P5-SCRATCH-PATHS.txt"
    listed_paths = [
        line for line in path_list.read_text(encoding="utf-8").splitlines() if line
    ]
    if listed_paths != expected_paths:
        failures.append("P0--P5 exact path-list drift")

    manifest_path = TMP / "P0-P5-SCRATCH-MANIFEST.sha256"
    manifest_rows: list[tuple[str, str]] = []
    for line in manifest_path.read_text(encoding="utf-8").splitlines():
        if not line:
            continue
        parts = line.split("  ", 1)
        if len(parts) != 2 or not re.fullmatch(r"[0-9a-f]{64}", parts[0]):
            failures.append(f"malformed manifest row: {line}")
            continue
        manifest_rows.append((parts[1], parts[0]))
    if [path for path, _ in manifest_rows] != expected_paths:
        failures.append("P0--P5 manifest path/order drift")
    for path, expected_hash in manifest_rows:
        candidate = ROOT / path
        if not candidate.is_file():
            failures.append(f"manifest member missing: {path}")
            continue
        actual_hash = hashlib.sha256(candidate.read_bytes()).hexdigest()
        if actual_hash != expected_hash:
            failures.append(
                f"manifest byte drift: {path} expected={expected_hash} actual={actual_hash}"
            )

    tracked_decl_names: dict[str, list[str]] = {}
    for path in (ROOT / "YangMills").rglob("*.lean"):
        text = path.read_text(encoding="utf-8-sig")
        for name in DECL.findall(text):
            tracked_decl_names.setdefault(name, []).append(path.relative_to(ROOT).as_posix())

    proposed_seen: dict[str, str] = {}
    declaration_count = 0
    for index, (scratch_name, tracked_name) in enumerate(SOURCES):
        source = TMP / scratch_name
        target = ROOT / "YangMills" / "RG" / tracked_name
        if not source.is_file():
            failures.append(f"missing scratch source: tmp/{scratch_name}")
            continue
        if target.exists():
            failures.append(f"tracked module already exists: {target.relative_to(ROOT)}")

        text = source.read_text(encoding="utf-8-sig")
        declarations = DECL.findall(text)
        declaration_count += len(declarations)
        for old in declarations:
            new = promoted_name(old)
            previous = proposed_seen.get(new)
            if previous is not None:
                failures.append(f"proposed-name collision: {new} ({previous}, {scratch_name})")
            else:
                proposed_seen[new] = scratch_name
            for collision in tracked_decl_names.get(new, []):
                failures.append(f"tracked declaration collision: {new} in {collision}")

        audit_name = source.stem + "Audit.lean"
        audit = TMP / audit_name
        if not audit.is_file():
            failures.append(f"missing sibling audit: tmp/{audit_name}")
        else:
            audit_text = audit.read_text(encoding="utf-8-sig")
            expected_audit_import = [f"tmp.{source.stem}"]
            actual_audit_import = IMPORT.findall(audit_text)
            if actual_audit_import != expected_audit_import:
                failures.append(
                    f"sibling audit import mismatch {audit_name}: "
                    f"expected={expected_audit_import} actual={actual_audit_import}"
                )
            printed = PRINT.findall(audit_text)
            if printed != declarations:
                failures.append(
                    f"sibling audit order/scope mismatch {scratch_name}: "
                    f"expected={declarations} actual={printed}"
                )

        imports = IMPORT.findall(text)
        if index == 0:
            expected_tmp: list[str] = []
        else:
            expected_tmp = [f"tmp.{Path(SOURCES[index - 1][0]).stem}"]
        actual_tmp = [item for item in imports if item.startswith("tmp.")]
        if actual_tmp != expected_tmp:
            failures.append(
                f"tmp import mismatch {scratch_name}: expected={expected_tmp} actual={actual_tmp}"
            )

    # The aggregate endpoint audit is intentionally additional to the sibling
    # audit of P3PhysicalGreenRecurrence.
    aggregate = TMP / "P3PhysicalGreenRecurrenceAggregateAudit.lean"
    if not aggregate.is_file():
        failures.append("missing aggregate P3 endpoint audit")
    else:
        aggregate_imports = IMPORT.findall(aggregate.read_text(encoding="utf-8-sig"))
        aggregate_prints = tuple(PRINT.findall(aggregate.read_text(encoding="utf-8-sig")))
        if aggregate_imports != ["tmp.P3PhysicalGreenRecurrence"]:
            failures.append(f"aggregate P3 import drift: {aggregate_imports}")
        if aggregate_prints != P3_AGGREGATE:
            failures.append(
                f"aggregate P3 readout drift: expected={P3_AGGREGATE} "
                f"actual={aggregate_prints}"
            )

    if failures:
        print("P0_P5_PROMOTION_STATIC_FAIL")
        for failure in failures:
            print(f"- {failure}")
        return 1

    print(
        "P0_P5_PROMOTION_STATIC_OK "
        f"sources={len(SOURCES)} declarations={declaration_count} "
        f"unique_promoted_names={len(proposed_seen)} sibling_audits={len(SOURCES)} "
        "aggregate_audits=1 "
        f"manifest_members={len(manifest_rows)} "
        f"manifest_sha256={hashlib.sha256(manifest_path.read_bytes()).hexdigest().upper()}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
