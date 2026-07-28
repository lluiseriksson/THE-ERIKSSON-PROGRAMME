from __future__ import annotations

import sys
from fractions import Fraction
from math import factorial
from pathlib import Path

import mpmath as mp
from flint import arb, ctx


ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))

import surface_remainder_s2_delta8_exact as delta8  # noqa: E402
import surface_remainder_s2_spatial5_exact as exact  # noqa: E402
import surface_remainder_y_carrier as raw  # noqa: E402


def test_delta_eight_scaffold() -> None:
    ctx.prec = 180
    delta8.check()
    nodes = delta8.spatial_nodes(16, 2)
    assert nodes[0] == 0 and nodes[-1].overlaps(arb("1.2"))
    assert all(nodes[index] < nodes[index + 1] for index in range(16))
    nodes_three_halves = delta8.spatial_nodes(16, Fraction(3, 2))
    assert all(
        nodes_three_halves[index] < nodes_three_halves[index + 1]
        for index in range(16)
    )


def test_series_algebra_matches_flint_polynomial_identity() -> None:
    x = delta8.sconst(arb(2))
    x[1] = delta8.jet(arb(3))
    x[2] = delta8.jet(arb(5))
    square = delta8.smul(x, x)
    assert square[0].get(0, 0) == 4
    assert square[1].get(0, 0) == 12
    assert square[2].get(0, 0) == 29


def test_integrand_coefficients_zero_through_four_match_tjet() -> None:
    ctx.prec = 180
    delta, t, s, alpha = arb(1) / 20, arb("2.9"), arb("0.4"), arb("0.7")
    series_prefactors, series_phase = delta8.physical_moment_parts(
        delta, t, delta8.variable_x(s), delta8.variable_y(alpha)
    )
    series_values = {
        name: delta8.smul(value, delta8.sexp(series_phase))
        for name, value in series_prefactors.items()
    }
    tjet_prefactors, tjet_phase = exact.physical_moment_parts_tjet(
        exact.tjet(delta, 1),
        t,
        exact.variable_x(s),
        exact.variable_y(alpha),
    )
    tjet_values = {
        name: exact.jmul(value, exact.jexp(tjet_phase)).get(0, 0)
        for name, value in tjet_prefactors.items()
    }
    for name in delta8.NAMES:
        derivatives = tjet_values[name].derivatives()
        for order in range(5):
            assert series_values[name][order].get(0, 0).overlaps(
                derivatives[order] / arb(factorial(order))
            )


def test_orders_zero_through_thirteen_and_delta_eight_against_mpmath() -> None:
    ctx.prec = 220
    mp.mp.dps = 90
    point = mp.mpf(30)
    for family, function in (
        ("A", lambda z: mp.exp(-z) * mp.besseli(1, z) / z),
        ("B", lambda z: mp.exp(-z) * mp.besseli(2, z) / z**2),
    ):
        values = exact.scaled_bessel_derivatives(arb(str(point)), family, 13)
        for order, value in enumerate(values):
            assert value.contains(arb(str(mp.diff(function, point, order))))

    delta, t, s, alpha = (
        mp.mpf(1) / 20,
        mp.mpf("2.9"),
        mp.mpf("0.4"),
        mp.mpf("0.7"),
    )
    prefactors, phase = delta8.physical_moment_parts(
        arb(str(delta)),
        arb(str(t)),
        delta8.variable_x(arb(str(s))),
        delta8.variable_y(arb(str(alpha))),
    )
    values = {
        name: delta8.smul(value, delta8.sexp(phase))
        for name, value in prefactors.items()
    }
    for name in delta8.NAMES:
        for order in range(delta8.PREC):
            expected = mp.diff(
                lambda d: raw.scalar_raw(d, t, s, alpha, name),
                delta,
                order,
            ) / mp.factorial(order)
            assert values[name][order].get(0, 0).contains(arb(str(expected))), (
                name,
                order,
                values[name][order].get(0, 0),
                expected,
            )
