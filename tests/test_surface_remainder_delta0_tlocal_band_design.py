from fractions import Fraction

from flint import arb, ctx

import surface_remainder_delta0_derivative_tail as old
import surface_remainder_delta0_outer_domain_v6 as uniform
import surface_remainder_delta0_r4_extension_009_tlocal_probe as probe
import surface_remainder_delta0_tlocal_band_design as local


def test_local_rate_recovers_global_rate_at_right_endpoint():
    ctx.prec = 120
    cmin = arb(2).sqrt()/2
    assert local.gaussian_rate_from_cmin(cmin).overlaps(old.gaussian_rate())
    assert local.cmin_from_t_hi(arb.pi()).overlaps(cmin)


def test_local_band_is_no_larger_than_uniform_band():
    ctx.prec = 120
    cap = Fraction(9, 1000)
    split = Fraction(1181, 1000)
    radius_u, band_u = uniform.direct_moving_band_value_coefficients_from(
        cap, split)
    radius_l, band_l = local.direct_moving_band_value_coefficients_from(
        cap, split, arb(1))
    assert radius_l == radius_u
    assert all(band_l[name] < band_u[name] for name in band_u)


def test_invalid_local_domains_are_rejected():
    ctx.prec = 120
    try:
        local.cmin_from_t_hi(arb.pi()+1)
    except ValueError:
        pass
    else:
        raise AssertionError("t endpoint outside [0,pi] was accepted")


def test_tlocal_witness_contract_is_frozen():
    assert probe.DELTA_MAX == Fraction(9, 1000)
    assert probe.PHYSICAL_INNER == Fraction(1181, 1000)
    assert probe.WITNESS_INDEX == 50
    assert probe.GRID == 192
