import mpmath as mp

from flint import arb, ctx

import surface_right_edge_five_family_central_design as central
from surface_remainder_arb_jet2 import hull


def test_normalized_bessel_chain_contains_direct_derivatives():
    ctx.prec = 160
    mp.mp.dps = 100
    delta = arb(1)/125
    angle = arb(1)/5
    sine, cosine = angle.sin(), angle.cos()
    v = 2*cosine
    for family, orders in (("I1", (1, 3, 5)), ("I0", (2, 4))):
        for order in orders:
            derivatives = central.cosine_derivatives(
                sine, cosine, arb(2), arb(1), order)
            enclosure = central.normalized_composite(
                delta, v, derivatives, family, order)
            nu = 1 if family == "I1" else 0
            dd = mp.mpf(1)/125
            aa = mp.mpf(1)/5
            z = 2*mp.cos(aa)/dd
            exact = (dd**order*mp.exp(-z)/mp.sqrt(dd)
                     *mp.diff(lambda u: mp.besseli(
                         nu, 2*mp.cos(u)/dd), aa, order))
            assert enclosure.contains(arb(str(exact)))


def test_elementary_series_contains_direct_values():
    ctx.prec = 160
    x = arb(3)/500
    y = x*x
    s = central.elementary_series(y, "s")
    j = central.elementary_series(y, "j")
    assert s.overlaps(x.sin()/x)
    assert j.overlaps((x.sin()-x*x.cos())/x**3)


def test_zero_based_delta_sqrt_encloses_endpoints():
    ctx.prec = 160
    delta = hull(arb(0), arb(1)/125)
    root = central.nonnegative_sqrt(delta)
    assert root.contains(arb(0))
    assert root.contains((arb(1)/125).sqrt())


def test_halfline_reduced_values_apply_manifested_chart_intersection():
    ctx.prec = 160
    invz = hull(arb(0), arb(1)/20)
    v = hull(arb(1)/2, arb(2))
    i0, i1 = central.reduced_values(invz, v)
    assert i0.is_finite() and i1.is_finite()


def test_symmetric_q_sum_covers_both_halves():
    ctx.prec = 160
    value = central.q_sum(lambda q: q**2, arb(1), 20)
    assert value.contains(arb(2)/3)
