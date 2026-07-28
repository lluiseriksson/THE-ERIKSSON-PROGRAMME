from __future__ import annotations

import sys
from fractions import Fraction
from pathlib import Path

from flint import arb, ctx


ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))

import audit_surface_full_moment_y_normalization as audit_mod  # noqa: E402
import surface_remainder_delta0_companion_error as companion  # noqa: E402
import surface_remainder_delta0_outer_domain_v2 as outer  # noqa: E402


def test_every_registered_full_moment_helper_uses_physical_normalization() -> None:
    checked = audit_mod.audit(ROOT)
    assert len(checked) == 16


def test_scalar_error_charge_corrects_the_exact_historical_factor() -> None:
    ctx.prec = 180
    delta_max = arb("0.01")
    kd_lower = arb(2)
    moment_upper = arb(7)
    error = arb("0.2")
    corrected = companion.normalized_y_error_from_moment_coefficient(
        delta_max, kd_lower, moment_upper, error
    )
    d5 = delta_max**5
    actual_lower = kd_lower-error*d5
    delta_b = 4*moment_upper*error+2*error**2*d5
    inverse = (
        error*(2*moment_upper+error*d5)
        /(actual_lower**2*kd_lower**2)
    )
    bracket = (
        delta_b/actual_lower**2
        + 2*moment_upper**2*inverse
    )
    cmin = arb(2).sqrt()/2
    historical = bracket/(2*cmin)
    assert corrected.overlaps(8*cmin*historical)


def test_componentwise_error_charge_has_full_moment_factor_four() -> None:
    ctx.prec = 180
    delta_max = Fraction(1, 200)
    kd_lower = arb(2)
    moments = {
        "kd": arb(2),
        "kf": arb(3),
        "hdd": arb(5),
        "hdf": arb(7),
    }
    errors = {
        "kd": arb("0.1"),
        "kf": arb("0.2"),
        "hdd": arb("0.3"),
        "hdf": arb("0.4"),
    }
    corrected = outer.normalized_y_error_from_moment_coefficients(
        delta_max, kd_lower, moments, errors
    )
    dmax = arb(delta_max.numerator)/delta_max.denominator
    d5 = dmax**5
    actual_lower = kd_lower-errors["kd"]*d5
    delta_b = (
        moments["kd"]*errors["hdf"]
        + moments["hdf"]*errors["kd"]
        + errors["kd"]*errors["hdf"]*d5
        + moments["kf"]*errors["hdd"]
        + moments["hdd"]*errors["kf"]
        + errors["kf"]*errors["hdd"]*d5
    )
    inverse = (
        errors["kd"]*(2*moments["kd"]+errors["kd"]*d5)
        /(actual_lower**2*kd_lower**2)
    )
    nominal_b = (
        moments["kd"]*moments["hdf"]
        + moments["kf"]*moments["hdd"]
    )
    expected = 4*(delta_b/actual_lower**2+nominal_b*inverse)
    assert corrected.overlaps(expected)
