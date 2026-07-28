"""Validate the current-head K4 gap-branch t-box pair.

This is a local candidate validator only.  It deliberately cannot promote
K4, S1'''/S2''', G2, or G6.
"""
from __future__ import annotations

import hashlib
import json
from pathlib import Path

from flint import arb, ctx

ROOT = Path(__file__).resolve().parents[1]
STEM = "scripts/surface_remainder_k4_tbox_gapbranch_t300_310"
NAMES = (
    "muF_main", "nuD_main", "nuF_main", "MD_mirror", "MF_mirror",
    "MD2r_mirror", "MDFr_mirror",
)


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def parse(path: Path) -> dict:
    lines = path.read_text(encoding="utf-8").replace("\r\n", "\n").splitlines()
    assert lines[0] == "K4 CENTERED T-BOX PROBE TRANSCRIPT"
    assert any(line.startswith("CONFIG delta 1/25:81/2000 t 3:31/10") for line in lines)
    assert lines[-2] == "K4 CENTERED T-BOX PROBE PASS"
    assert "no K4/S1'''/S2'''/G6 promotion" in lines[-1]
    cells = [json.loads(line[5:]) for line in lines if line.startswith("CELL ")]
    assert len(cells) == 2304
    assert all(cell["fallback"] in (True, False) for cell in cells)
    fallback = int(next(line.split()[1] for line in lines if line.startswith("FALLBACKS ")))
    assert fallback == sum(bool(cell["fallback"]) for cell in cells)
    fractions = json.loads(next(line.split(" ", 1)[1]
                                for line in lines if line.startswith("FRACTIONS ")))
    parsed = {name: arb(fractions[name]) for name in NAMES}
    assert all(value.is_finite() and value.upper() < 1 for value in parsed.values())
    return {"cells": len(cells), "fallbacks": fallback, "fractions": fractions}


def main() -> int:
    ctx.prec = 180
    production = ROOT / f"{STEM}.txt"
    replay = ROOT / f"{STEM}_rerun.txt"
    assert production.is_file() and replay.is_file()
    assert production.read_bytes() == replay.read_bytes()
    result = parse(production)
    dependencies = (
        "scripts/certify_surface_remainder_k4_t_box_probe.py",
        "scripts/certify_surface_remainder_k4_centered_band.py",
        "scripts/surface_remainder_centered_delta_carrier.py",
        "scripts/surface_bessel_gap_taylor.py",
        "scripts/surface_bessel_entire_lowz.py",
        "scripts/surface_bessel_integral_remainder.py",
    )
    for relative in dependencies:
        assert (ROOT / relative).is_file()
    print("K4 GAP-BRANCH T-BOX VALIDATION PASS")
    print("CELLS", result["cells"], "FALLBACKS", result["fallbacks"])
    print("PRODUCTION/REPLAY BYTE EQUALITY PASS")
    print("DEPENDENCY HASHES", json.dumps({p: digest(ROOT / p) for p in dependencies}, sort_keys=True))
    print("CANDIDATE ONLY; NO K4/S1'''/S2'''/G2/G6 PROMOTION")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
