from __future__ import annotations

import sys
from pathlib import Path

import sympy as sp
from flint import arb, ctx


ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))

import probe_surface_k2_kd_covariance as probe  # noqa: E402


def test_kd_covariance_identity_is_exact() -> None:
    kd, kf, hdd, hdf, delta, r0 = sp.symbols(
        "kd kf hdd hdf delta r0", nonzero=True
    )
    mean_a = kf / kd
    mean_g = (hdd / kd - r0) / delta
    mean_ag = (hdf / kd - r0 * kf / kd) / delta
    covariance_y = 4 * (mean_ag - mean_a * mean_g)
    determinant_y = 4 * (kd * hdf - kf * hdd) / (delta * kd**2)
    assert sp.simplify(covariance_y - determinant_y) == 0


def test_pointwise_g_has_a_removable_delta_zero_limit() -> None:
    ctx.prec = 180
    point = probe.kd_covariance_point(
        arb(0),
        probe.T,
        probe.old.sd(arb("1.0"), 1),
        probe.old.sd(arb("0.5"), 0, 1),
    )
    assert point["weight"].v.coeffs()[0] > 0
    assert all(
        coefficient.is_finite()
        for coefficient in point["g"].v.coeffs()
    )


def test_endpoint_weight_cell_mass_is_strictly_positive() -> None:
    ctx.prec = 180
    weight = probe.endpoint_weight_cell_mass(
        probe.T, arb(0), arb(1), arb(0), arb(1)
    )
    assert arb(weight.lower()) > 0


def test_gruss_charge_uses_deviation_radii_without_extra_quarter() -> None:
    ctx.prec = 180
    charge = probe.within_cell_covariance_radius(
        arb(3), arb("0.2"), arb("0.5")
    )
    assert charge.overlaps(arb("0.3"))
