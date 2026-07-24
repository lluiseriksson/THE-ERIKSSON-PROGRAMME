"""Audit the current-dependency K4 t-box regeneration.

This validates only the regenerated, candidate-only archive.  It is kept
separate from the historical audit so stale provenance cannot be silently
accepted.  No K4/S1'''/S2'''/G2/G6 promotion is performed.
"""

from fractions import Fraction
from pathlib import Path
import importlib.util

ROOT = Path(__file__).resolve().parents[1]
AUDIT = ROOT / "scripts" / "audit_surface_remainder_k4_tbox_candidate_union_20260723.py"
PI_HI = Fraction(31415927, 10_000_000)
UNITS = [(f"{i:03d}_{i+1:03d}", Fraction(i, 100), Fraction(i + 1, 100))
         for i in range(300, 314)] + [("314_pi", Fraction(157, 50), PI_HI)]


def load_audit():
    spec = importlib.util.spec_from_file_location("k4_candidate_audit", AUDIT)
    module = importlib.util.module_from_spec(spec)
    assert spec.loader is not None
    spec.loader.exec_module(module)
    return module


def main() -> None:
    audit = load_audit()
    cursor = Fraction(3)
    total = 0
    for unit, lo, hi in UNITS:
        assert lo == cursor
        path = ROOT / "scripts" / f"surface_remainder_k4_tbox_{unit}_20260723_current_regen.txt"
        replay = ROOT / "scripts" / f"surface_remainder_k4_tbox_{unit}_20260723_current_regen_rerun.txt"
        assert path.exists() and replay.exists(), unit
        assert path.read_bytes() == replay.read_bytes(), unit
        fractions = audit.check(path, lo, hi)
        assert all(audit.arb(value).upper() < 1 for value in fractions.values())
        total += 2304
        cursor = hi
    assert cursor == PI_HI
    print("K4 CURRENT-REGEN T-BOX AUDIT PASS")
    print("units", len(UNITS), "cells", total, "domain", "3", str(PI_HI))
    print("PRODUCTION/REPLAY BYTE EQUALITY PASS")
    print("CANDIDATE ONLY; NO K4/S1'''/S2'''/G2/G6 PROMOTION")


if __name__ == "__main__":
    main()
