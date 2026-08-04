from fractions import Fraction

from flint import arb, ctx

import surface_remainder_delta0_band_gap_design as gap
import surface_remainder_delta0_derivative_tail as old
import surface_remainder_delta0_r4_extension_009_band_gap_probe as probe


def test_band_rate_strictly_improves_global_endpoint_rate():
    ctx.prec = 120
    cmin = arb(2).sqrt()/2
    rate = gap.gaussian_rate_on_band(cmin, Fraction(1181, 1000))
    assert rate > old.gaussian_rate()


def test_endpoint_band_coefficients_are_strictly_smaller():
    ctx.prec = 120
    cap = Fraction(9, 1000)
    split = Fraction(1181, 1000)
    radius, values = gap.direct_moving_band_value_coefficients_from(
        cap, split, arb.pi())
    assert radius == Fraction(62, 5)
    assert all(value.is_finite() and value > 0 for value in values.values())


def test_band_gap_witness_contract_is_frozen():
    assert probe.DELTA_MAX == Fraction(9, 1000)
    assert probe.PHYSICAL_INNER == Fraction(1181, 1000)
    assert probe.WITNESS_INDEX == 157
    assert probe.GRID == 384

