from __future__ import annotations

import sys
from pathlib import Path

import mpmath as mp
from flint import arb, ctx


ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))

from surface_remainder_centered_prefactor import Dual  # noqa: E402
import surface_remainder_y_carrier as old  # noqa: E402
import surface_remainder_s2_spatial5_exact as exact  # noqa: E402


def test_delta_jet_polynomial_and_chain_rule() -> None:
    x = exact.djet(arb(2), arb(3), arb(5))
    square = x * x
    assert square.c0 == 4
    assert square.c1 == 12
    assert square.c2 == 29
    exponential = x.exp()
    assert exponential.c0.overlaps(arb(2).exp())
    assert exponential.c1.overlaps(arb(2).exp() * 3)
    assert exponential.c2.overlaps(arb(2).exp() * (5 + arb(9) / 2))


def test_extended_recurrence_matches_independent_differentiation() -> None:
    ctx.prec = 200
    mp.mp.dps = 80
    for family, function in (
        ("A", lambda z: mp.exp(-z) * mp.besseli(1, z) / z),
        ("B", lambda z: mp.exp(-z) * mp.besseli(2, z) / z**2),
    ):
        for point in (mp.mpf(5), mp.mpf(30), mp.mpf(100)):
            values = exact.scaled_bessel_derivatives(arb(str(point)), family, 9)
            for order, value in enumerate(values):
                expected = mp.diff(function, point, order)
                assert value.contains(arb(str(expected))), (
                    family,
                    point,
                    order,
                    value,
                    expected,
                )


def test_extended_recurrence_overlaps_existing_orders_zero_through_four() -> None:
    ctx.prec = 180
    from surface_remainder_centered_prefactor import outer_derivatives

    box = arb("30 +/- 1")
    for family in ("A", "B"):
        current = outer_derivatives(box, family)
        extended = exact.scaled_bessel_derivatives(box, family, 7)
        assert all(a.overlaps(b) for a, b in zip(current, extended))


def test_endpoint_orientation_and_complete_monotonicity() -> None:
    ctx.prec = 180
    for family in ("A", "B"):
        values = exact.scaled_bessel_derivatives(arb("50 +/- 20"), family, 7)
        for order, value in enumerate(values):
            assert value.lower() > 0 if order % 2 == 0 else value.upper() < 0


def test_exact_physical_integrand_matches_old_delta_jets() -> None:
    ctx.prec = 200
    delta, t = arb(1) / 15, arb("2.9")
    for s, alpha in ((arb("0.4"), arb("0.7")), (arb("1.1"), arb("0.2"))):
        prefactors, phase = exact.physical_moment_parts(
            delta, t, exact.variable_x(s), exact.variable_y(alpha)
        )
        exponential = exact.jexp(phase)
        values = {
            name: exact.djet(exact.jmul(value, exponential).get(0, 0))
            for name, value in prefactors.items()
        }
        old_values = old.raw_integrand_jets(
            delta, t, Dual(s), Dual(alpha)
        )
        for name in ("KD", "KF", "HDD", "HDF"):
            assert values[name].c0.overlaps(old_values[name].c0.v)
            assert values[name].c1.overlaps(old_values[name].c1.v)
            assert values[name].c2.overlaps(old_values[name].c2.v)


def test_one_cell_is_finite() -> None:
    ctx.prec = 160
    calibration = exact.calibration_jet(
        arb(1) / 20,
        arb(1) / 20,
        (arb("-0.0411533885"), arb("-0.816255981"), arb("0.217165721")),
    )
    values = exact.centered_cell(
        arb(1) / 20,
        arb("2.9"),
        arb("0.3"),
        arb("0.45"),
        arb("0.45"),
        arb("0.6"),
        calibration,
    )
    assert all(value.is_finite() for value in values.values())


def test_tjet_integrand_matches_independent_first_four_derivatives() -> None:
    ctx.prec = 200
    mp.mp.dps = 70
    delta, t, s, alpha = (
        mp.mpf(1) / 20,
        mp.mpf("2.9"),
        mp.mpf("0.4"),
        mp.mpf("0.7"),
    )
    prefactors, phase = exact.physical_moment_parts_tjet(
        exact.tjet(arb(str(delta)), 1),
        arb(str(t)),
        exact.variable_x(arb(str(s))),
        exact.variable_y(arb(str(alpha))),
    )
    exponential = exact.jexp(phase)
    for name, prefactor in prefactors.items():
        value = exact.jmul(prefactor, exponential).get(0, 0)
        for order, ball in enumerate(value.derivatives()):
            expected = mp.diff(
                lambda d: old.scalar_raw(d, t, s, alpha, name),
                delta,
                order,
            )
            assert ball.contains(arb(str(expected))), (
                name,
                order,
                ball,
                expected,
            )
