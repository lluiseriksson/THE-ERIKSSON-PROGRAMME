from __future__ import annotations

import sys
from pathlib import Path

import pytest
from flint import arb, arb_series, ctx

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))

import surface_remainder_delta0_series_design as design  # noqa: E402


@pytest.mark.parametrize("c_text", ("0.75", "0.83"))
def test_full_moment_assembler_does_not_apply_h_over_k_twice(
    c_text: str,
) -> None:
    ctx.prec = 180
    c = arb(c_text)
    kd_dimensionless = arb_series([arb(2), arb(3), arb(5)], design.PREC)
    kf_dimensionless = arb_series([arb(7), arb(11), arb(13)], design.PREC)
    hdd_dimensionless = arb_series(
        [arb(17), arb(19), arb(23)], design.PREC
    )
    hdf_dimensionless = arb_series(
        [arb(29), arb(31), arb(37)], design.PREC
    )
    k_constant = arb(3)
    h_constant = k_constant / (8 * c)
    moments = {
        "kd": k_constant * kd_dimensionless,
        "kf": k_constant * kf_dimensionless,
        "hdd": h_constant * hdd_dimensionless,
        "hdf": h_constant * hdf_dimensionless,
    }
    bilinear_dimensionless = (
        kd_dimensionless * hdf_dimensionless
        - kf_dimensionless * hdd_dimensionless
    )
    coefficients = bilinear_dimensionless.coeffs() + [arb(0)] * design.PREC
    shifted = arb_series(
        [coefficients[k + 1] for k in range(design.PREC - 2)],
        design.PREC - 2,
    )
    expected = shifted / (2 * c * kd_dimensionless**2)
    actual = design.assemble_y_derivatives(moments, arb(4) * c.acos())
    assert all(
        left.overlaps(right)
        for left, right in zip(actual.coeffs(), expected.coeffs())
    )


def test_full_moment_assembler_has_the_required_kernel_homogeneity() -> None:
    ctx.prec = 180
    t = arb("2.9")
    moments = {
        "kd": arb_series([arb(2), arb(3), arb(5)], design.PREC),
        "kf": arb_series([arb(7), arb(11), arb(13)], design.PREC),
        "hdd": arb_series([arb(17), arb(19), arb(23)], design.PREC),
        "hdf": arb_series([arb(29), arb(31), arb(37)], design.PREC),
    }
    k_scale, h_scale = arb(5), arb(7)
    scaled = {
        "kd": k_scale * moments["kd"],
        "kf": k_scale * moments["kf"],
        "hdd": h_scale * moments["hdd"],
        "hdf": h_scale * moments["hdf"],
    }
    base = design.assemble_y_derivatives(moments, t)
    actual = design.assemble_y_derivatives(scaled, t)
    expected = (h_scale / k_scale) * base
    assert all(
        left.overlaps(right)
        for left, right in zip(actual.coeffs(), expected.coeffs())
    )


def test_old_double_scaled_formula_differs_by_exact_factor() -> None:
    ctx.prec = 180
    t = arb("2.9")
    c = (t / 4).cos()
    moments = {
        "kd": arb_series([arb(2), arb(1)], design.PREC),
        "kf": arb_series([arb(3), arb(5)], design.PREC),
        "hdd": arb_series([arb(7), arb(11)], design.PREC),
        "hdf": arb_series([arb(13), arb(17)], design.PREC),
    }
    bilinear = moments["kd"] * moments["hdf"] - moments["kf"] * moments["hdd"]
    coefficients = bilinear.coeffs() + [arb(0)] * design.PREC
    shifted = arb_series(
        [coefficients[k + 1] for k in range(design.PREC - 2)],
        design.PREC - 2,
    )
    corrected = design.assemble_y_derivatives(moments, t)
    historical = shifted / (2 * c * moments["kd"] ** 2)
    assert all(
        left.overlaps(8 * c * right)
        for left, right in zip(corrected.coeffs(), historical.coeffs())
    )
