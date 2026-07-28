"""Audit the current-head regeneration of the six centred lower K4 bands."""

import hashlib
import json
from pathlib import Path

from flint import arb

from surface_remainder_complement_l3_smoke import NAMES

ROOT = Path(__file__).resolve().parents[1]
UNITS = (
    "k4_00275_00280", "k4_00280_00285", "k4_00285_00290",
    "k4_00290_00295", "k4_00295_0030", "k4_0030",
)


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def parse(path: Path):
    lines = path.read_text(encoding="utf-8").splitlines()
    assert lines[0] == "K4 CENTERED BAND TRANSCRIPT"
    assert any("CANDIDATE PASS" in line for line in lines)
    assert "promotion" in lines[-1]
    for line in lines:
        if line.startswith("DEPENDENCY "):
            _, relative, digest = line.split()
            assert digest == sha256(ROOT / relative), (path.name, relative)
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
    head = next(line.split()[-1] for line in lines if line.startswith("PROVENANCE git_head "))
    return len(cells), head


def main() -> None:
    total = 0
    heads = set()
    for unit in UNITS:
        production = ROOT / "scripts" / f"surface_remainder_k4_{unit}_current_regen.txt"
        replay = ROOT / "scripts" / f"surface_remainder_k4_{unit}_current_regen_rerun.txt"
        assert production.exists() and replay.exists(), unit
        assert production.read_bytes() == replay.read_bytes(), unit
        count, head = parse(production)
        count2, head2 = parse(replay)
        assert count == count2 and head == head2
        total += count
        heads.add(head)
    assert len(heads) == 1
    assert total == 6 * 9216
    print(f"K4 CENTERED LOWER CURRENT-REGEN AUDIT PASS: 6 units, {total} cells")
    print(f"source_head {next(iter(heads))}")
    print("PRODUCTION/REPLAY BYTE EQUALITY PASS")
    print("CANDIDATE ONLY; NO K4/G2/G6/S1'''/S2''' PROMOTION")


if __name__ == "__main__":
    main()
