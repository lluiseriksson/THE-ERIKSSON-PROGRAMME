#!/usr/bin/env python3
"""Read-only audit and rendering of the restartable Step 8b.23 brick order."""

from __future__ import annotations

import hashlib
import re
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
TMP = ROOT / "tmp"
SCHEDULE: tuple[tuple[str, tuple[str, ...]], ...] = (
    (
        "A",
        (
            "BalabanCMP89CenteredBrillouinAffineSlice",
            "BalabanCMP89CenteredUnitCubeTorusQuotient",
            "BalabanCMP89CenteredTorusFourierPhase",
            "BalabanCMP89NormalizedBrillouinToTorusMeasure",
        ),
    ),
    (
        "B",
        (
            "BalabanCMP89Eq248GreenMassUniformHolomorphy",
            "BalabanCMP89Eq248DisplayedGreenVectorPeriodicity",
            "BalabanCMP89Eq248CenteredGreenTorus",
        ),
    ),
    (
        "C",
        (
            "BalabanCMP99CenteredTorusSampleDictionary",
            "BalabanCMP99CenteredTorusPhysicalGreenSampleTransport",
        ),
    ),
    (
        "D",
        (
            "BalabanCMP89Eq248GreenOneCoordinateContourShift",
            "BalabanCMP89Eq248GreenProductContourTelescope",
            "BalabanCMP89Eq248MassUniformGreenBound",
            "BalabanCMP89Eq248MassUniformNormalizedGreenBound",
        ),
    ),
    (
        "E",
        (
            "BalabanCMP89CenteredTorusGreenCoefficientPhase",
            "BalabanCMP89CenteredTorusGreenCoefficientDictionary",
            "BalabanCMP89SignedLatticeL1TotalSum",
            "BalabanCMP89CenteredGreenFourierSummability",
            "BalabanCMP99PhysicalGreenFiniteGridAliasing",
        ),
    ),
    (
        "F",
        (
            "BalabanCMP89CenteredPeriodicL1ResidueSum",
            "BalabanCMP99CenteredPeriodicEndpointDictionary",
            "BalabanCMP99PhysicalGreenZeroResidueBound",
            "BalabanCMP99DiagonalFiniteGreenOwnerBound",
        ),
    ),
)
DECL = re.compile(
    r"(?m)^(?:(?:noncomputable|protected)\s+)?"
    r"(?:def|abbrev|theorem|lemma|structure|class)\s+([A-Za-z0-9_.'’]+)"
)
PRINT = re.compile(r"(?m)^#print axioms YangMills\.RG\.([A-Za-z0-9_.'’]+)")
IMPORT = re.compile(r"(?m)^import\s+([^\s]+)")


def main() -> int:
    failures: list[str] = []
    flattened = [(unit, name) for unit, names in SCHEDULE for name in names]
    if len(flattened) != 22 or len({name for _, name in flattened}) != 22:
        failures.append("declared schedule is not 22 unique modules")

    scoped_sources = {
        path.name.removesuffix(".draft.lean")
        for raw in (TMP / "STEP8B23-ALL-PATHS.txt").read_text(encoding="utf-8-sig").splitlines()
        if raw.strip()
        for path in [ROOT / raw.strip()]
        if not path.name.endswith("Audit.draft.lean")
    }
    scheduled_names = {name for _, name in flattened}
    if scoped_sources != scheduled_names:
        failures.append(
            "schedule/path scope mismatch: "
            f"missing={sorted(scoped_sources - scheduled_names)} "
            f"extra={sorted(scheduled_names - scoped_sources)}"
        )

    positions = {name: index for index, (_, name) in enumerate(flattened, start=1)}
    rendered: list[str] = []
    total_declarations = 0
    total_dependencies = 0
    for index, (unit, name) in enumerate(flattened, start=1):
        source = TMP / f"{name}.draft.lean"
        audit = TMP / f"{name}Audit.draft.lean"
        if not source.is_file() or not audit.is_file():
            failures.append(f"missing pair: {name}")
            continue
        declarations = DECL.findall(source.read_text(encoding="utf-8-sig"))
        prints = PRINT.findall(audit.read_text(encoding="utf-8-sig"))
        if declarations != prints:
            failures.append(
                f"ordered declaration/audit mismatch: {name} "
                f"decls={declarations} prints={prints}"
            )
        total_declarations += len(declarations)

        imports = IMPORT.findall(source.read_text(encoding="utf-8-sig"))
        dependencies = sorted(
            {
                imported.removeprefix("YangMills.RG.")
                for imported in imports
                if imported.removeprefix("YangMills.RG.") in scheduled_names
            },
            key=positions.__getitem__,
        )
        for dependency in dependencies:
            if positions[dependency] >= index:
                failures.append(f"forward schedule dependency: {name} -> {dependency}")
        total_dependencies += len(dependencies)
        deps = ",".join(dependencies) if dependencies else "-"
        rendered.append(f"{index:02d}\t{unit}\t{name}\t{len(declarations)}\t{deps}\n")

    if total_declarations != 173:
        failures.append(f"declaration total {total_declarations}, expected 173")
    if failures:
        print("STEP8B23_BRICK_SCHEDULE_FAIL")
        for failure in failures:
            print(f"- {failure}")
        return 1

    payload = "".join(rendered)
    schedule_sha256 = hashlib.sha256(payload.encode("utf-8")).hexdigest().upper()
    print(
        "STEP8B23_BRICK_SCHEDULE_OK "
        f"bricks=22 declarations={total_declarations} internal_dependencies={total_dependencies} "
        f"schedule_sha256={schedule_sha256}"
    )
    print("ORDER\tUNIT\tMODULE\tAXIOM_BLOCKS\tINTERNAL_DEPENDENCIES")
    print(payload, end="")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
