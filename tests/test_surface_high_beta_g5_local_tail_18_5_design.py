import sys
from fractions import Fraction
from pathlib import Path

from flint import arb, ctx


ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))

import certify_surface_high_beta_g5_local_tail_18_5 as cert
import certify_surface_high_beta_g5_lambda4 as uniform


def test_frozen_local_tail_partition() -> None:
    assert cert.UNITS == tuple(
        (start, start + 10) for start in range(100, 180, 10)
    )


def test_local_tail_geometry() -> None:
    cert.verify_geometry()
    assert Fraction(9, 1000) * Fraction(18, 5) / 2 < Fraction(3, 80)


def test_local_near_charge_is_the_same_formula_at_four_and_smaller_at_18_5() -> None:
    ctx.prec = 140
    delta_max = arb(9) / 1000
    local_u, local_b = cert.near_bounds_local(
        delta_max, arb(18) / 5
    )
    at_four_u, at_four_b = cert.near_bounds_local(delta_max, arb(4))
    uniform_u, uniform_b = uniform.near_bounds_lambda4(delta_max)
    for order in (1, 3, 5):
        assert at_four_u[order].overlaps(uniform_u[order])
        assert local_u[order].upper() < at_four_u[order].lower()
    for order in (2, 4):
        assert at_four_b[order].overlaps(uniform_b[order])
        assert local_b[order].upper() < at_four_b[order].lower()
