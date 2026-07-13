from fractions import Fraction

import surface_remainder_delta0_outer_domain_v4 as v4
import surface_remainder_delta0_outer_domain_v5 as v5


def test_v5_domain_and_v4_isolation():
    assert v5._require_delta(Fraction(1, 125)) > 0
    try:
        v4._require_delta(Fraction(1, 125))
    except ValueError:
        pass
    else:
        raise AssertionError("v4 domain leaked")


def test_v5_annulus_is_local():
    assert v5.annulus_derivative_bounds_box_to is not v4.annulus_derivative_bounds_box_to
