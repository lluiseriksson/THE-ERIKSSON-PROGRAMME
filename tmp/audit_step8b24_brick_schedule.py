#!/usr/bin/env python3
"""Read-only audit of the complete 39-brick Step 8b.23/8b.24 queue."""

from __future__ import annotations

import hashlib
import re
from pathlib import Path

from audit_step8b23_brick_schedule import SCHEDULE as STEP8B23_SCHEDULE


ROOT = Path(__file__).resolve().parents[1]
TMP = ROOT / "tmp"
STEP8B24_SCHEDULE: tuple[tuple[str, str], ...] = (
    ("S1a", "BalabanCMP99SourceSeparatedGeneratedFlatPhysicalAmbientGreen"),
    ("S1b", "BalabanCMP99SourceSeparatedGeneratedFlatPhysicalAmbientGreenComplexification"),
    ("S2a", "BalabanCMP99SourceSeparatedGeneratedFlatPhysicalStep7bCarrier"),
    ("S2b", "BalabanCMP99SourceSeparatedGeneratedFlatPhysicalStep7bPrecisionDictionary"),
    ("S3a", "BalabanCMP99SourceFlatQprimePhysicalFineSymbolMassZeroNoncentral"),
    ("S3b", "BalabanCMP99SourceSeparatedGeneratedFlatPhysicalGreenIdentification"),
    ("S4", "BalabanCMP99SourceSeparatedGeneratedFlatPhysicalGreenFourierEndpoint"),
    ("C0", "BalabanCMP99SourceSeparatedGeneratedFlatPhysicalEndpointIntegrand"),
    ("C1a", "BalabanCMP99FlatComplexFibrePointSourceFourierReconstruction"),
    ("C1b", "BalabanCMP99SourceSeparatedGeneratedFlatPhysicalPointSourceEndpoint"),
    ("C2", "BalabanCMP99SourceSeparatedGeneratedFlatPhysicalZeroResidueAliasing"),
    ("C3", "BalabanCMP99SourceSeparatedGeneratedFlatPhysicalPointSourceZeroResidue"),
    ("C4a", "BalabanCMP99SourceFineToCoarseCenteredOwnerDictionary"),
    ("C4b", "BalabanCMP99SourceSeparatedGeneratedFlatPhysicalPointSourceOwnerBound"),
    ("C5", "BalabanCMP99SourceSeparatedGeneratedFlatPhysicalSourceOwnerBound"),
    ("C6a", "BalabanCMP99SourceSeparatedGeneratedFlatPhysicalPointSourceB0"),
    ("C6b", "BalabanCMP99SourceSeparatedGeneratedFlatPhysicalLocalizedFieldB0"),
)
OWNERSHIP_MODULE = "BalabanCMP99SourceFlatQprimePhysicalFineSymbolMassZeroNoncentral"
DECL = re.compile(
    r"(?m)^(?:(?:noncomputable|protected)\s+)?"
    r"(?:def|abbrev|theorem|lemma|structure|class)\s+([A-Za-z0-9_.'’]+)"
)
PRINT = re.compile(r"(?m)^#print axioms YangMills\.RG\.([A-Za-z0-9_.'’]+)")
IMPORT = re.compile(r"(?m)^import\s+([^\s]+)")
COMMENT_IMPORT = re.compile(r"(?m)^--\s*import\s+([^\s]+)")


def main() -> int:
    failures: list[str] = []
    first = [(unit, name) for unit, names in STEP8B23_SCHEDULE for name in names]
    schedule = first + list(STEP8B24_SCHEDULE)
    names = [name for _, name in schedule]
    if len(schedule) != 39 or len(set(names)) != 39:
        failures.append(f"schedule scope={len(schedule)}/{len(set(names))}; expected 39/39")

    scoped_sources = {
        path.name.removesuffix(".draft.lean")
        for raw in (TMP / "STEP8B24-ALL-PATHS.txt").read_text(encoding="utf-8-sig").splitlines()
        if raw.strip()
        for path in [ROOT / raw.strip()]
        if not path.name.endswith("Audit.draft.lean")
    }
    if scoped_sources != set(names):
        failures.append(
            "schedule/path scope mismatch: "
            f"missing={sorted(scoped_sources - set(names))} "
            f"extra={sorted(set(names) - scoped_sources)}"
        )

    positions = {name: index for index, name in enumerate(names, start=1)}
    rendered: list[str] = []
    declaration_total = 0
    dependency_total = 0
    promotion_import_total = 0
    for index, (unit, name) in enumerate(schedule, start=1):
        source = TMP / f"{name}.draft.lean"
        audit = TMP / f"{name}Audit.draft.lean"
        if not source.is_file() or not audit.is_file():
            failures.append(f"missing pair: {name}")
            continue
        source_text = source.read_text(encoding="utf-8-sig")
        declarations = DECL.findall(source_text)
        prints = PRINT.findall(audit.read_text(encoding="utf-8-sig"))
        if declarations != prints:
            failures.append(f"ordered declaration/audit mismatch: {name}")
        declaration_total += len(declarations)

        commented = COMMENT_IMPORT.findall(source_text)
        promotion_import_total += len(commented)
        imports = IMPORT.findall(source_text) + commented
        dependencies = sorted(
            {
                imported.removeprefix("YangMills.RG.")
                for imported in imports
                if imported.removeprefix("YangMills.RG.") in positions
            },
            key=positions.__getitem__,
        )
        for dependency in dependencies:
            if positions[dependency] >= index:
                failures.append(f"forward schedule dependency: {name} -> {dependency}")
        dependency_total += len(dependencies)
        ownership = "move-old-owner" if name == OWNERSHIP_MODULE else "-"
        deps = ",".join(dependencies) if dependencies else "-"
        rendered.append(
            f"{index:02d}\t{unit}\t{name}\t{len(declarations)}\t{ownership}\t{deps}\n"
        )

    if declaration_total != 222:
        failures.append(f"declaration total {declaration_total}, expected 222")
    if dependency_total != 48:
        failures.append(f"dependency total {dependency_total}, expected 48")
    if promotion_import_total != 23:
        failures.append(f"source promotion imports {promotion_import_total}, expected 23")
    ownership_position = positions.get(OWNERSHIP_MODULE)
    if ownership_position != 27:
        failures.append(f"ownership move position {ownership_position}, expected 27")

    if failures:
        print("STEP8B24_BRICK_SCHEDULE_FAIL")
        for failure in failures:
            print(f"- {failure}")
        return 1

    payload = "".join(rendered)
    schedule_sha256 = hashlib.sha256(payload.encode("utf-8")).hexdigest().upper()
    print(
        "STEP8B24_BRICK_SCHEDULE_OK "
        f"bricks=39 declarations={declaration_total} dependencies={dependency_total} "
        f"source_promotion_imports={promotion_import_total} ownership_move_at=27 "
        f"schedule_sha256={schedule_sha256}"
    )
    print("ORDER\tUNIT\tMODULE\tAXIOM_BLOCKS\tSPECIAL_DELTA\tINTERNAL_DEPENDENCIES")
    print(payload, end="")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
