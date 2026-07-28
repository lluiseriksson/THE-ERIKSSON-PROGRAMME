from __future__ import annotations

import sys
from pathlib import Path

from flint import arb, ctx


ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT/"scripts"))

import certify_surface_k2_fixed_square_complex_geometry as cert  # noqa: E402


def test_complex_geometry_contract_is_fixed() -> None:
    assert cert.RHO.overlaps(arb(7)/1000)
    assert cert.SIDE == 12
    assert cert.TERMS == 5


def test_complex_geometry_has_strict_denominator_floors() -> None:
    ctx.prec = 180
    values = cert.bounds()
    assert values["d_floor"] > 0
    assert values["root_modulus_floor"] > 0
    assert values["one_plus_root_floor"] > 0
    assert values["a_polynomial_floor"] > 0
    assert values["b_polynomial_floor"] > 0
