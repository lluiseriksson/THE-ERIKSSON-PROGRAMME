from __future__ import annotations

import sys
from pathlib import Path

import mpmath as mp
from flint import arb, ctx


ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))

from surface_remainder_centered_prefactor import Dual  # noqa: E402
import surface_remainder_y_carrier as yc  # noqa: E402


def test_entire_w_derivatives_contain_independent_values() -> None:
    ctx.prec = 180
    mp.mp.dps = 70
    for family, fn in (
        ("G", lambda w: mp.hyper([], [2], w / 4) / 2),
        ("H", lambda w: mp.hyper([], [3], w / 4) / 8),
    ):
        box = arb("0 +/- 25")
        derivatives = yc.entire_w_derivatives(box, family)
        for sample in (mp.mpf(0), mp.mpf(1), mp.mpf(25)):
            for order in range(5):
                expected = mp.diff(fn, sample, order)
                assert derivatives[order].contains(arb(str(expected)))


def test_raw_jets_match_delta_derivatives_in_both_lanes() -> None:
    ctx.prec = 180
    mp.mp.dps = 70
    delta, t = mp.mpf(1) / 15, mp.mpf("2.9")
    for s, alpha in ((mp.mpf("0.4"), mp.mpf("0.7")),
                     (mp.pi, mp.mpf("0.02"))):
        values = yc.raw_integrand_jets(
            arb(str(delta)), arb(str(t)), Dual(arb(str(s))), Dual(arb(str(alpha)))
        )
        for name, value in values.items():
            expected = mp.diff(lambda d: yc.scalar_raw(d, t, s, alpha, name), delta, 2) / 2
            assert value.c2.v.contains(arb(str(expected))), (name, value.c2.v, expected)


def test_scaled_raw_parts_match_independent_delta_derivatives() -> None:
    ctx.prec = 180
    mp.mp.dps = 70
    delta, t = mp.mpf(1) / 15, mp.mpf("2.9")
    sigma, tau = mp.mpf("1.1"), mp.mpf("0.7")
    prefactors, phase = yc.scaled_raw_integrand_parts(
        arb(str(delta)), arb(str(t)), Dual(arb(str(sigma))), Dual(arb(str(tau)))
    )
    exponential = yc.jexp(phase)
    for name, prefactor in prefactors.items():
        value = yc.jmul(prefactor, exponential).c2.v

        def scaled_scalar(d: mp.mpf) -> mp.mpf:
            return d * yc.scalar_raw(
                d, t, mp.sqrt(d) * sigma, mp.sqrt(d) * tau, name
            )

        expected = mp.diff(scaled_scalar, delta, 2) / 2
        assert value.contains(arb(str(expected))), (name, value, expected)
