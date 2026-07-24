"""Audit the current-head regeneration of the 39 K4 positive bands.

This is deliberately separate from the historical validator: it consumes only
the ``*_current_regen`` production/replay pair and requires every dependency
hash to match the present checkout.  It records candidate evidence only.
"""

from fractions import Fraction
import hashlib
import json
from pathlib import Path

from flint import arb

from surface_remainder_complement_l3_smoke import NAMES

ROOT = Path(__file__).resolve().parents[1]
BANDS = {
    f"k4p_{i:02d}": (Fraction(61 + i, 2000), Fraction(62 + i, 2000))
    for i in range(39)
}
DEPS = (
    "scripts/certify_surface_remainder_k4_positive_0305_0500.py",
    "scripts/surface_remainder_centered_delta_integrator_design.py",
    "scripts/surface_remainder_centered_delta_carrier.py",
    "scripts/surface_remainder_complement_l3_smoke.py",
    "scripts/surface_remainder_complement.py",
    "docs/SURFACE-REMAINDER-K4-POSITIVE-0305-0500-PREREG.md",
)


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def parse(path: Path, unit: str):
    lines = path.read_text(encoding="utf-8").splitlines()
    assert lines[0] == "K4 POSITIVE 0305-0500 TRANSCRIPT"
    assert f"CONFIG unit {unit} " in lines[5]
    assert "K4 POSITIVE 0305-0500 CANDIDATE PASS" in lines
    assert "no K4/G2/G6/S1'''/S2''' promotion" in lines[-1]
    deps = {line.split()[1]: line.split()[2]
            for line in lines if line.startswith("DEPENDENCY ")}
    expected = {relative: sha256(ROOT / relative) for relative in DEPS}
    assert deps == expected, (path.name, deps, expected)
    cells = [json.loads(line[5:]) for line in lines if line.startswith("CELL ")]
    assert cells and [cell["index"] for cell in cells] == list(range(len(cells)))
    totals = json.loads(next(line[6:] for line in lines if line.startswith("TOTAL ")))
    fractions = json.loads(next(line[10:] for line in lines if line.startswith("FRACTIONS ")))
    recomputed = {name: arb(0) for name in NAMES}
    for cell in cells:
        assert set(cell["values"]) == set(NAMES)
        for name in NAMES:
            value = arb(cell["values"][name])
            assert value.is_finite()
            recomputed[name] += value
    for name in NAMES:
        assert arb(totals[name]).overlaps(recomputed[name])
        assert arb(fractions[name]).upper() < 1
    assert int(next(line.split()[1] for line in lines if line.startswith("CELLS "))) == len(cells)
    head = next(line.split()[-1] for line in lines
                if line.startswith("PROVENANCE git_head "))
    carrier = next(line.split()[2] for line in lines
                    if line.startswith("DEPENDENCY scripts/surface_remainder_centered_delta_carrier.py "))
    return len(cells), head, carrier


def main() -> None:
    total = 0
    heads = set()
    carriers = set()
    for unit in BANDS:
        production = ROOT / "scripts" / f"surface_remainder_{unit}_current_regen.txt"
        replay = ROOT / "scripts" / f"surface_remainder_{unit}_current_regen_rerun.txt"
        assert production.exists() and replay.exists(), unit
        assert production.read_bytes() == replay.read_bytes(), unit
        count, head, carrier = parse(production, unit)
        count2, head2, carrier2 = parse(replay, unit)
        assert count == count2 and head == head2 and carrier == carrier2
        total += count
        heads.add(head)
        carriers.add(carrier)
    assert len(heads) == 1, heads
    assert carriers == {sha256(ROOT / "scripts/surface_remainder_centered_delta_carrier.py")}
    assert total == 39 * 2304
    print(f"K4 POSITIVE CURRENT-REGEN AUDIT PASS: 39 units, {total} cells")
    print(f"source_head {next(iter(heads))} carrier {next(iter(carriers))}")
    print("PRODUCTION/REPLAY BYTE EQUALITY PASS")
    print("CANDIDATE ONLY; NO K4/G2/G6/S1'''/S2''' PROMOTION")


if __name__ == "__main__":
    main()
