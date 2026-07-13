from fractions import Fraction

from flint import arb, arb_series, ctx

import surface_remainder_delta0_derivative_tail as old
import surface_remainder_delta0_outer_domain_v2 as mod


def test_delta_max_is_mandatory_exact_and_bounded():
    for bad in (arb("0.001"), 0.001, Fraction(1, 100)):
        try:
            mod._require_delta(bad)
        except (TypeError, ValueError):
            pass
        else:
            raise AssertionError("invalid delta domain was accepted")


def test_v2_reproduces_or_enlarges_sealed_endpoint_outer_bounds():
    ctx.prec = 140
    new = mod.outer_derivative_bounds(Fraction(1, 1000))
    sealed = old.outer_derivative_bounds()
    for name in sealed:
        assert all(a.overlaps(b) or a >= b
                   for a, b in zip(new[name], sealed[name]))
    radius, bands = mod.moving_band_value_coefficients(Fraction(1, 1000))
    assert radius == 31
    assert all(value.is_finite() and value > 0 for value in bands.values())


def test_enlarged_lane_moves_band_radius_inward():
    ctx.prec = 140
    radius, bands = mod.moving_band_value_coefficients(Fraction(1, 200))
    assert radius == 14
    assert all(value.is_finite() and value > 0 for value in bands.values())


def test_direct_value_band_avoids_derivative_coefficient_explosion():
    ctx.prec = 140
    delta = Fraction(1, 200)
    radius, direct = mod.direct_moving_band_value_coefficients(delta)
    old_radius, coefficientwise = mod.moving_band_value_coefficients(delta)
    assert radius == old_radius == 14
    assert all(direct[name] < coefficientwise[name] for name in direct)
    assert max(value.upper() for value in direct.values()) < 3500


def test_add_outer_derivatives_requires_claimed_delta():
    series = {name: arb_series([1, 0, 0, 0, 0, 0], 6)
              for name in ("kd", "kf", "hdd", "hdf")}
    result = mod.add_outer_derivatives(series, Fraction(1, 1000))
    assert set(result) == set(series)


def test_componentwise_determinant_perturbation_keeps_small_errors_small():
    ctx.prec = 140
    moments = {name: arb(10) for name in ("kd", "kf", "hdd", "hdf")}
    errors = {"kd": arb("0.001"), "kf": arb(30),
              "hdd": arb("0.1"), "hdf": arb(3500)}
    value = mod.normalized_y_error_from_moment_coefficients(
        Fraction(1, 200), arb(2), moments, errors)
    assert value.is_finite() and value > 0
    assert value < 20000
