from flint import arb, ctx

import surface_remainder_delta0_centered_series as mod
from surface_remainder_delta0_series_design import nominal_moment_series


def test_series_dual_product_rule():
    x, y = mod.sd(2, 1), mod.sd(3, 0, 1)
    value = mod.mul(x, y)
    assert value.v.coeffs()[0] == 6
    assert value.x.coeffs()[0] == 3
    assert value.y.coeffs()[0] == 2
    assert value.xy.coeffs()[0] == 1


def test_point_moments_overlap_sealed_nominal_series():
    ctx.prec = 120
    base, t, sigma, tau = arb("0.002"), arb("2.9"), arb("1.2"), arb("0.7")
    old = nominal_moment_series(base, t, sigma, tau)
    new = mod.moment_duals(base, t, mod.sd(sigma, 1), mod.sd(tau, 0, 1))
    for name in old:
        assert all(a.overlaps(b) for a, b in zip(
            old[name].coeffs(), new[name].v.coeffs()))


def test_root_floor_resolves_only_constant_coefficient():
    wide = mod.arb_series([arb("0 +/- 1"), arb("2 +/- 3")], mod.PREC)
    fixed = mod.apply_root2_floor(wide)
    assert fixed.coeffs()[0] > 0
    assert fixed.coeffs()[1].str(80) == wide.coeffs()[1].str(80)
