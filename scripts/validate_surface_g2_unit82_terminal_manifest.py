"""Validate the three-slice terminal direct-sign manifest."""

from __future__ import annotations

import hashlib
import json
from fractions import Fraction
from pathlib import Path

from flint import arb, ctx

from validate_surface_g2_unit82_terminal import validate

ROOT = Path(__file__).resolve().parents[1]


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> int:
    ctx.prec = 240
    manifest_path = ROOT / "run-manifests" / "surface-scaled-bulk-cwin3p2-unit82-terminal-20260725.json"
    manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    assert manifest["status"] == "terminal_direct_sign_certified"
    assert manifest["promotion"] == "NONE"
    units = manifest["units"]
    assert len(units) == 3
    expected = [(Fraction(275, 4), Fraction(1101, 16)),
                (Fraction(1101, 16), Fraction(1103, 16)),
                (Fraction(1103, 16), Fraction(69))]
    counts = []
    for unit, (lo, hi) in zip(units, expected):
        production = ROOT / unit["production"]["path"]
        replay = ROOT / unit["replay"]["path"]
        assert production.read_bytes() == replay.read_bytes()
        digest = sha(production)
        assert digest == unit["production"]["sha256"]
        assert digest == unit["replay"]["sha256"]
        counts.append(validate(production, lo, hi))
    for left, right in zip(units, units[1:]):
        assert Fraction(left["beta_domain"][1]) == Fraction(right["beta_domain"][0])
    assert sum(counts) == manifest["total_t_rows"]
    print("UNIT82 TERMINAL MANIFEST VALIDATION PASS",
          "beta", manifest["beta_union"], "t_rows", sum(counts))
    print("DIRECT SIGN COVER ONLY; NO H_TAIL/G2/G6 PROMOTION")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
