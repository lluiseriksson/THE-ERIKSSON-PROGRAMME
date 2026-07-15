from flint import arb, ctx
import mpmath as mp

import surface_remainder_carrier_jet as old
import surface_remainder_centered_delta_carrier as centered
import surface_remainder_complement as complement
from surface_remainder_tjet import TJet
from surface_remainder_arb_jet2 import hull


def assert_low_orders_overlap(new, previous):
    assert new.v.overlaps(previous.c0)
    assert new.d.overlaps(previous.c1)
    assert new.d2.overlaps(2*previous.c2)


def test_main_weighted_carriers_overlap_existing_jet2_backend():
    ctx.prec = 140
    delta, t, s, alpha = (arb(1)/20, arb("2.9"),
                          arb("0.8"), arb("0.8"))
    weight = complement.complement_weight_jet(
        delta, s, alpha, inside_physical_square=True)
    previous = {
        name: old.mul(weight, value)
        for name, value in old.carriers(delta, t, s, alpha).items()
    }
    current = centered.weighted_carriers(
        delta, t, s, alpha, mirror=False, inside_physical_square=True)
    assert current.keys() == previous.keys()
    for name in current:
        assert_low_orders_overlap(current[name], previous[name])


def test_mirror_weighted_carriers_overlap_existing_jet2_backend():
    ctx.prec = 140
    delta, t, s, alpha = (arb(1)/20, arb("2.9"),
                          arb("0.8"), arb("0.8"))
    weight = complement.complement_weight_jet(
        delta, s, alpha, inside_physical_square=True)
    previous = {
        name: old.mul(weight, value)
        for name, value in old.mirror_carriers(delta, t, s, alpha).items()
    }
    current = centered.weighted_carriers(
        delta, t, s, alpha, mirror=True, inside_physical_square=True)
    assert current.keys() == previous.keys()
    for name in current:
        assert_low_orders_overlap(current[name], previous[name])


def test_centered_second_derivative_formula_contains_quartic_range():
    center = TJet(arb(1), arb(4), arb(12), arb(24), arb(24))
    whole_box = TJet(arb(0), arb(0), arb(0), arb(0), arb(24))
    enclosure = centered.second_derivative_enclosure(
        center, whole_box, arb("0.1"))
    assert enclosure.contains(arb("9.72"))
    assert enclosure.contains(arb("14.52"))


def test_whole_delta_box_fourth_derivatives_are_finite():
    ctx.prec = 140
    delta = TJet(hull(arb("0.049"), arb("0.05")), arb(1))
    rows = centered.weighted_carriers(
        delta, arb("2.9"), arb("0.8"), arb("0.8"),
        mirror=False, inside_physical_square=True)
    assert all(value.d4.is_finite() for value in rows.values())


def exact_weighted_carriers(delta, t, s, alpha, mirror):
    c, s4 = mp.cos(t/4), mp.sin(t/4)
    beta = 1/delta
    if mirror:
        p, q = mp.cos(s/2)**2, mp.cos(alpha/2)**2
        radius = mp.sqrt(4*c**2*(1-p)*(1-q)+4*s4**2*p*q)
        phase = 2*beta*radius-4*beta*s4
        cos_s, cos_a = -mp.cos(s), -mp.cos(alpha)
    else:
        p, q = mp.sin(s/2)**2, mp.sin(alpha/2)**2
        radius = mp.sqrt(4*c**2*(1-p)*(1-q)+4*s4**2*p*q)
        phase = 2*beta*radius-4*beta*c
        cos_s, cos_a = mp.cos(s), mp.cos(alpha)
    z = 2*beta*radius
    aa = mp.exp(-z)*mp.besseli(1, z)/z
    bb = mp.exp(-z)*mp.besseli(2, z)/z**2
    kernel = 2*beta**mp.mpf("2.5")*aa*mp.exp(phase)
    hb = beta**mp.mpf("1.5")*bb*mp.exp(phase)
    d = 2*(1-p-q)
    cc = 2*c**2-1
    n = cc*mp.cos(2*s)+cos_a*(cc*cos_s-1+cos_s**2)
    f = n-cc*d
    u = (s**2+alpha**2)/delta
    qq = (u-16)/84
    chi = 1-10*qq**3+15*qq**4-6*qq**5
    weight = 1-chi
    if mirror:
        return {
            "MD_mirror": weight*kernel*d,
            "MF_mirror": weight*kernel*f,
            "MD2r_mirror": weight*beta**2*hb*d**2,
            "MDFr_mirror": weight*beta**2*hb*d*f,
        }
    return {
        "muF_main": weight*beta*kernel*f,
        "nuD_main": weight*beta**2*hb*d**2,
        "nuF_main": weight*beta**3*hb*d*f,
    }


def test_third_and_fourth_derivatives_contain_multiprecision_oracle():
    ctx.prec = 180
    mp.mp.dps = 80
    delta, t, s, alpha = (mp.mpf("0.05"), mp.mpf("2.9"),
                          mp.mpf("0.8"), mp.mpf("0.8"))
    for mirror in (False, True):
        rows = centered.weighted_carriers(
            arb("0.05"), arb("2.9"), arb("0.8"), arb("0.8"),
            mirror=mirror, inside_physical_square=True)
        for name, row in rows.items():
            function = lambda value, n=name, m=mirror: (
                exact_weighted_carriers(value, t, s, alpha, m)[n])
            third = arb(str(mp.diff(function, delta, 3)))
            fourth = arb(str(mp.diff(function, delta, 4)))
            assert row.d3.contains(third), (name, row.d3, third)
            assert row.d4.contains(fourth), (name, row.d4, fourth)


def test_cutoff_crossing_is_rejected():
    delta = TJet(arb("0.05 +/- 0.001"), arb(1))
    try:
        centered.cutoff_jet(delta, arb("0.9"), arb(0))
    except ValueError as exc:
        assert "cutoff junction" in str(exc)
    else:
        raise AssertionError("a cutoff-crossing cell must subdivide")


def test_centered_delta_spatial_cell_is_finite_and_contains_center_track():
    ctx.prec = 140
    dlo, dhi, t = arb("0.049"), arb("0.05"), arb("2.9")
    slo, shi = arb("0.79"), arb("0.81")
    alo, ahi = arb("0.79"), arb("0.81")
    rows = centered.centered_delta_cell(
        dlo, dhi, t, slo, shi, alo, ahi, True)
    midpoint = (dlo+dhi)/2
    from surface_remainder_complement_l3_smoke import centered_cell
    retained = centered_cell(midpoint, t, slo, shi, alo, ahi, True)
    assert rows.keys() == retained.keys()
    assert all(value.is_finite() for value in rows.values())
    assert all(rows[name].contains(retained[name]) for name in rows)


def test_scaled_main_carriers_overlap_independent_jet2_backend():
    ctx.prec = 140
    delta, t, sigma, tau = (arb("0.03"), arb("2.9"),
                            arb("1.2"), arb("2.1"))
    previous = old.scaled_carriers(delta, t, sigma, tau)
    current = centered.scaled_main_carriers(delta, t, sigma, tau)
    assert current.keys() == previous.keys()
    for name in current:
        assert_low_orders_overlap(current[name], previous[name])


def test_scaled_centered_cell_is_finite():
    ctx.prec = 140
    values = centered.direct_scaled_centered_delta_cell(
        arb("0.02"), arb("0.0205"), arb("2.9"),
        arb(0), arb("0.2"), arb(0), arb("0.2"))
    assert all(value.is_finite() for value in values.values())
