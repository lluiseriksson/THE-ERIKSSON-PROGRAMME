from __future__ import annotations

import sys
from fractions import Fraction
from math import factorial
from pathlib import Path

import mpmath as mp
from flint import arb, ctx

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))

import surface_remainder_centered_delta_carrier as old  # noqa: E402
import surface_remainder_s1_delta8_exact as exact  # noqa: E402
import surface_remainder_s2_delta8_exact as base  # noqa: E402
from surface_remainder_spatial_jet3 import variable_x, variable_y  # noqa: E402


def test_s1_scaffold_and_budgets() -> None:
    ctx.prec = 140
    exact.check()
    assert set(exact.NAMES) == set(exact.BUDGETS)
    assert exact.DELTA_FINAL == Fraction(1, 15)


def _series_values(parts, phase):
    exponential = base.sexp(phase)
    return {
        name: base.smul(value, exponential)
        for name, value in parts.items()
    }


def test_main_coefficients_match_independent_tjet() -> None:
    ctx.prec = 180
    delta, t, s, alpha = arb("0.05"), arb("2.9"), arb("0.4"), arb("0.7")
    parts, phase = exact.main_carrier_parts(
        delta, t, variable_x(s), variable_y(alpha)
    )
    values = _series_values(parts, phase)
    reference = old.main_carriers(delta, t, s, alpha)
    for name in exact.MAIN_NAMES:
        derivatives = reference[name].derivatives()
        for order in range(5):
            assert values[name][order].get(0, 0).overlaps(
                derivatives[order] / arb(factorial(order))
            )


def test_mirror_coefficients_match_independent_tjet() -> None:
    ctx.prec = 180
    delta, t, s, alpha = arb("0.05"), arb("2.9"), arb("0.4"), arb("0.7")
    parts, phase = exact.mirror_carrier_parts(
        delta, t, variable_x(s), variable_y(alpha)
    )
    values = _series_values(parts, phase)
    reference = old.mirror_carriers(delta, t, s, alpha)
    for name in exact.MIRROR_NAMES:
        derivatives = reference[name].derivatives()
        for order in range(5):
            assert values[name][order].get(0, 0).overlaps(
                derivatives[order] / arb(factorial(order))
            )


def test_delta_eight_point_coefficients_against_mpmath() -> None:
    ctx.prec = 180
    mp.mp.dps = 70
    delta, t, s, alpha = (
        mp.mpf("0.05"),
        mp.mpf("2.9"),
        mp.mpf("0.4"),
        mp.mpf("0.7"),
    )
    parts, phase = exact.main_carrier_parts(
        arb(str(delta)),
        arb(str(t)),
        variable_x(arb(str(s))),
        variable_y(arb(str(alpha))),
    )
    values = _series_values(parts, phase)

    def mu_f(d):
        beta = 1 / d
        c = mp.cos(t / 4)
        p, q = mp.sin(s / 2) ** 2, mp.sin(alpha / 2) ** 2
        radius = mp.sqrt(
            4 * c**2 * (1 - p) * (1 - q)
            + 4 * mp.sin(t / 4) ** 2 * p * q
        )
        z = 2 * beta * radius
        scaled_a = mp.e**(-z) * mp.besseli(1, z) / z
        kernel = 2 * beta ** mp.mpf("2.5") * scaled_a
        cc = 2 * c**2 - 1
        x, y = mp.cos(s), mp.cos(alpha)
        fluctuation = (x - 1) * (
            cc * (2 * x + 1) + y * (x + cc + 1)
        )
        return beta * kernel * fluctuation * mp.e ** (
            beta * (2 * radius - 4 * c)
        )

    for order in range(base.PREC):
        reference = mp.diff(mu_f, delta, order) / mp.factorial(order)
        assert values["muF_main"][order].get(0, 0).overlaps(
            arb(str(reference))
        )


def test_half_second_transport_factor_on_exponential() -> None:
    ctx.prec = 160
    center, radius = arb("0.04"), arb("0.0005")
    center_coefficients = [
        center.exp() / arb(factorial(order)) for order in range(base.PREC)
    ]
    box = arb("0.04 +/- 0.0005")
    box_coefficients = [
        box.exp() / arb(factorial(order)) for order in range(base.PREC)
    ]
    enclosure = exact._half_second_transport(
        center_coefficients, box_coefficients, radius
    )
    truth = (box.exp() / 2)
    assert enclosure.overlaps(truth)


def test_one_spatial_cell_is_finite() -> None:
    ctx.prec = 140
    values = exact.centered_cell(
        arb("0.05"),
        arb("2.9"),
        arb("0"),
        arb("0.15"),
        arb("0"),
        arb("0.15"),
    )
    assert set(values) == set(exact.NAMES)
    assert all(
        coefficient.is_finite()
        for coefficients in values.values()
        for coefficient in coefficients
    )
