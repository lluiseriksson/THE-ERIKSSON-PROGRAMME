from __future__ import annotations

import sys
from pathlib import Path

import mpmath as mp
from flint import arb, ctx


ROOT = Path(__file__).resolve().parents[1]
SCRIPTS = ROOT / "scripts"
sys.path.insert(0, str(SCRIPTS))

import surface_remainder_carrier_jet as carrier  # noqa: E402
import surface_remainder_centered_prefactor as centered  # noqa: E402
import surface_remainder_complement as complement  # noqa: E402
import surface_remainder_complement_l3_smoke as l3_smoke  # noqa: E402


def test_fixed_domain_complement_contract() -> None:
    complement.check()


def test_fixed_physical_mirror_jets_contain_independent_derivatives() -> None:
    ctx.prec = 160
    mp.mp.dps = 60
    delta, t = mp.mpf(1) / 15, mp.mpf("2.9")
    sd, ad = mp.mpf("1.1"), mp.mpf("0.7")
    jets = carrier.mirror_carriers(
        arb(str(delta)), arb(str(t)), arb(str(sd)), arb(str(ad))
    )
    for name, jet in jets.items():
        expected = mp.diff(
            lambda d: carrier.scalar_mirror_carrier(d, t, sd, ad, name),
            delta,
            2,
        ) / 2
        assert jet.c2.contains(arb(str(expected))), (name, jet.c2, expected)


def test_spatial_delta_jets_match_independent_physical_carriers() -> None:
    ctx.prec = 160
    mp.mp.dps = 60
    delta, t = mp.mpf(1) / 15, mp.mpf("2.9")
    s, alpha = mp.mpf("1.1"), mp.mpf("0.7")
    for mirror, scalar in (
        (False, carrier.scalar_carrier),
        (True, carrier.scalar_mirror_carrier),
    ):
        values = centered.physical_carriers(
            arb(str(delta)),
            arb(str(t)),
            centered.Dual(arb(str(s)), arb(1)),
            centered.Dual(arb(str(alpha)), arb(0), arb(1)),
            mirror=mirror,
        )
        for name, value in values.items():
            expected = mp.diff(lambda d: scalar(d, t, s, alpha, name), delta, 2) / 2
            assert value.c2.v.contains(arb(str(expected))), (name, value.c2.v, expected)
        first_name = next(iter(values))

        def delta_second(x: mp.mpf, y: mp.mpf) -> mp.mpf:
            return mp.diff(lambda d: scalar(d, t, x, y, first_name), delta, 2) / 2

        expected_xx = mp.diff(lambda x: delta_second(x, alpha), s, 2)
        assert values[first_name].c2.xx.contains(arb(str(expected_xx)))


def test_complement_weight_vanishes_on_the_registered_core() -> None:
    weight = complement.complement_weight_jet(
        arb(1) / 15, arb("0.2"), arb("0.3"), inside_physical_square=True
    )
    assert weight.c0 == 0
    assert weight.c1 == 0
    assert weight.c2 == 0


def test_junction_hull_contains_both_piecewise_sides() -> None:
    delta = arb(1) / 15
    crossing = complement.cutoff_jet_enclosure(
        delta, arb("1.02 +/- 0.02"), arb("0.2 +/- 0.02")
    )
    for s in (mp.mpf("1.00"), mp.mpf("1.04")):
        u = (s**2 + mp.mpf("0.2") ** 2) / (mp.mpf(1) / 15)
        if u <= 16:
            expected = mp.mpf(1)
        elif u >= 100:
            expected = mp.mpf(0)
        else:
            q = (u - 16) / 84
            expected = 1 - 10 * q**3 + 15 * q**4 - 6 * q**5
        assert crossing.c0.contains(arb(str(expected)))


def test_complement_l3_coarse_smoke_is_finite() -> None:
    totals = l3_smoke.complement_second_coefficients(16)
    assert all(value.is_finite() for value in totals.values())
