from flint import arb, ctx

import surface_remainder_positive_pairwise_probe as mod
from surface_remainder_tjet import tjet


def row(value):
    return [tjet(value)]+[tjet(0)]*(mod.PREC-1)


def test_pairwise_grouping_matches_point_determinant():
    ctx.prec = 100
    cells = [
        {"KD": row(2), "KF": row(3), "HDD": row(5), "HDF": row(7)},
        {"KD": row(11), "KF": row(13), "HDD": row(17), "HDF": row(19)},
        {"KD": row(23), "KF": row(29), "HDD": row(31), "HDF": row(37)},
    ]
    totals = mod.summed_moments(cells)
    expected = mod.engine._sadd(
        mod.engine._smul(totals["KD"], totals["HDF"]),
        mod.engine._sneg(mod.engine._smul(totals["KF"], totals["HDD"])))
    actual = mod.pairwise_numerator(cells)
    assert all(a.v == b.v for a, b in zip(actual, expected))


def test_antisymmetrized_integrand_identity_at_points():
    kx, hx, dx, fx = map(arb, (2, 3, 5, 7))
    ky, hy, dy, fy = map(arb, (11, 13, 17, 19))
    ordered = (kx*dx*hy*dy*fy-kx*fx*hy*dy**2
               +ky*dy*hx*dx*fx-ky*fy*hx*dx**2)
    antisymmetric = ((dx*fy-fx*dy)*(kx*hy*dy-ky*hx*dx))
    assert ordered == antisymmetric
