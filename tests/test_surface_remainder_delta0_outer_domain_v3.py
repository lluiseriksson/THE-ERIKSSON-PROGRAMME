from fractions import Fraction

from flint import ctx

import surface_remainder_delta0_outer_domain_v2 as v2
import surface_remainder_delta0_outer_domain_v3 as mod


def test_v3_domain_is_exact_and_does_not_mutate_v2_contract():
    assert mod._require_delta(Fraction(3, 500)) > 0
    try:
        mod._require_delta(Fraction(7, 1000))
    except ValueError:
        pass
    else:
        raise AssertionError("v3 accepted an unregistered larger lane")
    try:
        v2._require_delta(Fraction(3, 500))
    except ValueError:
        pass
    else:
        raise AssertionError("v2 domain was mutated")


def test_v3_band_radius_is_twelve_and_finite():
    ctx.prec = 140
    radius, bands = mod.direct_moving_band_value_coefficients(
        Fraction(3, 500))
    assert radius == 12
    assert all(value.is_finite() and value > 0 for value in bands.values())
    # The temporary v3 domain must always be restored.
    try:
        v2._require_delta(Fraction(3, 500))
    except ValueError:
        pass
    else:
        raise AssertionError("v2 domain leaked after a v3 call")
