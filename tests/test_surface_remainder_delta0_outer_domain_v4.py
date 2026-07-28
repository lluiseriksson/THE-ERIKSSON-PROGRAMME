from fractions import Fraction
import surface_remainder_delta0_outer_domain_v3 as v3
import surface_remainder_delta0_outer_domain_v4 as mod
import surface_remainder_delta0_r4_extension_007_probe as probe

def test_v4_domain_and_v3_isolation():
    assert mod._require_delta(Fraction(7,1000))>0
    try: v3._require_delta(Fraction(7,1000))
    except ValueError: pass
    else: raise AssertionError("v3 domain leaked")

def test_v4_band_radius_is_13p1():
    radius,bands=mod.direct_moving_band_value_coefficients_from(Fraction(7,1000),Fraction(11,10))
    assert radius==Fraction(131,10)
    assert all(v.is_finite() and v>0 for v in bands.values())

def test_v4_preserves_incremental_core_boxes():
    assert probe.CORE_BOXES == (
        (Fraction(0), Fraction(1,200)),
        (Fraction(1,200), Fraction(3,500)),
        (Fraction(3,500), Fraction(7,1000)))


def test_v4_annulus_implementation_is_not_the_v3_wrapped_function():
    assert (mod.annulus_derivative_bounds_box_to
            is not v3.annulus_derivative_bounds_box_to)
    assert mod.MAX_DELTA == Fraction(7,1000)
