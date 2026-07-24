"""Validate one K4 t-box probe and an optional byte-identical replay."""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path

from flint import arb, ctx


ROOT = Path(__file__).resolve().parents[1]
NAMES = (
    "muF_main", "nuD_main", "nuF_main", "MD_mirror",
    "MF_mirror", "MD2r_mirror", "MDFr_mirror",
)


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def validate(path: Path, expected_cells: int) -> None:
    lines = path.read_text(encoding="utf-8").splitlines()
    assert lines[0] == "K4 CENTERED T-BOX PROBE TRANSCRIPT"
    assert "SCOPE candidate t-box only; no K4/S1'''/S2'''/G6 promotion" in lines
    assert lines[-2] == "K4 CENTERED T-BOX PROBE PASS"
    cells = []
    for line in lines:
        if line.startswith("DEPENDENCY "):
            _, rel, digest = line.split()
            assert sha256(ROOT / rel) == digest
        elif line.startswith("CELL "):
            cells.append(json.loads(line[5:]))
    assert len(cells) == expected_cells
    assert lines[-1].startswith("SCOPE ")
    fractions = json.loads(next(line.split(" ", 1)[1]
                                for line in lines if line.startswith("FRACTIONS ")))
    for name in NAMES:
        assert arb(fractions[name]).upper() < 1, (name, fractions[name])
    total = json.loads(next(line.split(" ", 1)[1]
                            for line in lines if line.startswith("TOTAL ")))
    assert set(total) == set(NAMES)
    print("K4 T-BOX PROBE VALIDATION PASS", path.relative_to(ROOT))


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("production", type=Path)
    parser.add_argument("replay", type=Path)
    parser.add_argument("--cells", type=int, default=9216)
    parser.add_argument("--precision", type=int, default=140)
    args = parser.parse_args()
    ctx.prec = args.precision
    production = (ROOT / args.production).resolve()
    replay = (ROOT / args.replay).resolve()
    production.relative_to(ROOT)
    replay.relative_to(ROOT)
    assert production.read_bytes() == replay.read_bytes()
    validate(production, args.cells)
    print("K4 T-BOX PRODUCTION/REPLAY BYTE EQUALITY PASS")
    print("CANDIDATE ONLY; NO K4/S1'''/S2'''/G6 PROMOTION")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
