"""Validate every production/replay pair in the order-24 terminal manifest."""

from __future__ import annotations

import hashlib
import json
from fractions import Fraction
from pathlib import Path

from validate_surface_g2_mid24_terminal import validate

ROOT = Path(__file__).resolve().parents[1]
MANIFEST = ROOT / "run-manifests" / "surface-scaled-bulk-cwin3p2-mid24-terminal-20260725.json"


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> int:
    manifest = json.loads(MANIFEST.read_text(encoding="utf-8"))
    assert manifest["status"] == "terminal_direct_sign_certified"
    assert manifest["promotion"] == "NONE"
    assert manifest["beta_union"] == ["241/4", "275/4"]
    units = manifest["units"]
    assert len(units) == 34
    previous = None
    rows = 0
    for unit in units:
        production = ROOT / unit["production"]["path"]
        replay = ROOT / unit["replay"]["path"]
        assert production.read_bytes() == replay.read_bytes()
        assert sha(production) == unit["production"]["sha256"]
        assert sha(replay) == unit["replay"]["sha256"]
        lo, hi = map(Fraction, unit["beta_domain"])
        count = validate(production, lo, hi)
        assert count == unit["t_rows"]
        assert previous is None or previous == lo
        previous = hi
        rows += count
    assert previous == Fraction(275, 4)
    assert rows == manifest["total_t_rows"]
    print("MID24 TERMINAL MANIFEST VALIDATION PASS",
          "units", len(units), "rows", rows, "beta", manifest["beta_union"])
    print("DIRECT SIGN COVER ONLY; NO H_TAIL/G2/G6 PROMOTION")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
