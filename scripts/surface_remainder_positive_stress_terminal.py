"""Terminal judge for the last K2 half-delta stress box.

This closes one born ``(delta,t)`` box only.  It deliberately does not claim
the 49-by-158 positive cover or G2.
"""

import hashlib
from pathlib import Path
import platform
import subprocess
from time import perf_counter

import flint
from flint import arb, ctx

import surface_remainder_companion_error_ordered as companion
import surface_remainder_positive_t_centered as remainder


ROOT = Path(__file__).resolve().parents[1]
DEPENDENCIES = (
    "scripts/surface_remainder_positive_stress_terminal.py",
    "scripts/surface_remainder_positive_t_centered.py",
    "scripts/surface_remainder_positive_physical_spatial3.py",
    "scripts/surface_remainder_positive_physical_series_design.py",
    "scripts/surface_remainder_arb_jet2.py",
    "scripts/surface_remainder_spatial_jet3.py",
    "scripts/surface_remainder_tjet.py",
    "scripts/surface_remainder_companion_error_ordered.py",
    "scripts/surface_remainder_delta0_companion_error.py",
    "scripts/surface_bessel_integral_remainder.py",
)


def sha256(path: Path, portable_lf: bool = False) -> str:
    data = path.read_bytes()
    if portable_lf:
        data = data.replace(b"\r\n", b"\n")
    return hashlib.sha256(data).hexdigest()


def residual_from_moments(moments, delta, t_eval, perturbation):
    series = remainder._sadd(
        remainder.assemble_y(moments, delta),
        remainder._sneg(remainder.exact_head(
            delta, remainder.tjet(t_eval, 1, 0))))
    # The sixth coefficient is reserved for the separate Lagrange charge.
    return series, remainder.evaluate_through(series, perturbation, 5)


def main() -> int:
    ctx.prec = 120
    started = perf_counter()
    delta_center = arb("0.04975")
    delta_lo, delta_hi = arb("0.0495"), arb("0.05")
    delta_box = remainder.spatial.hull(delta_lo, delta_hi)
    delta_radius = (delta_hi-delta_lo)/2
    perturbation = arb("0 +/- 0.00025")
    t_lo, t_hi = arb("2.9"), arb("2.92")
    t_center = (t_lo+t_hi)/2
    t_box = remainder.spatial.hull(t_lo, t_hi)
    t_radius = (t_hi-t_lo)/2

    print("K2 POSITIVE STRESS TERMINAL")
    print("python", platform.python_version(), "python-flint", flint.__version__,
          "arb_bits", ctx.prec)
    try:
        head = subprocess.check_output(
            ["git", "-c", f"safe.directory={ROOT.as_posix()}",
             "rev-parse", "HEAD"], cwd=ROOT, text=True).strip()
    except Exception as error:
        print("PROVENANCE FAILURE", repr(error))
        return 2
    print("git_head", head)
    for relative in DEPENDENCIES:
        path = ROOT/relative
        print("dependency", relative, "sha256", sha256(path),
              "sha256_lf", sha256(path, portable_lf=True))
    print("box delta", delta_lo, delta_hi, "t", t_lo, t_hi)
    print("grids center 32 box 8 delta_box 8 workers 4")

    center_moments, center_cells, _ = \
        remainder.parallel_uniform_moments(
            delta_center, t_center, grid=32, workers=4)
    _, center = residual_from_moments(
        center_moments, delta_center, t_center, perturbation)
    print("center cells", center_cells, "R", center.v, "D1", center.d,
          "D2", center.d2, "D3", center.d3, "D4", center.d4)

    box_moments, box_cells, _ = \
        remainder.parallel_uniform_moments(
            delta_center, t_box, grid=8, workers=4)
    _, box = residual_from_moments(
        box_moments, delta_center, t_box, perturbation)
    nominal = remainder.taylor4_value_enclosure(center, box, t_radius)
    print("t_box cells", box_cells, "D4", box.d4,
          "nominal_abs", nominal.abs_upper())

    delta_moments, delta_cells, delta_calibration = \
        remainder.parallel_uniform_moments(
            delta_box, t_box, grid=8, workers=4)
    delta_series, _ = residual_from_moments(
        delta_moments, delta_box, t_box, arb(0))
    delta_tail = arb(delta_series[6].v.abs_upper())*delta_radius**6
    print("delta_box cells", delta_cells, "coefficient6",
          delta_series[6].v, "delta_tail", delta_tail)

    # Coefficient zero of the track whose constant delta parameter is the
    # entire box directly encloses the nominal moments on that box.  It does
    # not rely on a truncated centre evaluation.
    original = remainder.uncalibrated_moments(
        delta_moments, delta_calibration)
    box_values = {name: series[0].v for name, series in original.items()}
    kd_lower = arb(box_values["KD"].lower())
    moment_abs = max(arb(value.abs_upper()) for value in box_values.values())
    if not kd_lower > 0:
        print("FAIL KD_NONPOSITIVE", kd_lower)
        return 1
    companion_coefficient = companion.normalized_y_error_coefficient(
        delta_hi, kd_lower, moment_abs, 6)
    companion_charge = companion_coefficient*delta_hi**6
    print("KD_lower", kd_lower, "moment_abs", moment_abs,
          "companion_coefficient", companion_coefficient,
          "companion_charge", companion_charge)

    total = arb(nominal.abs_upper())+delta_tail+companion_charge
    budget = arb(150000)*delta_lo**6
    margin = budget-total
    print("total", total, "budget", budget, "margin", margin)
    print("elapsed_seconds", perf_counter()-started)
    if not margin > 0:
        print("K2 POSITIVE STRESS TERMINAL FAIL")
        return 1
    print("K2 POSITIVE STRESS TERMINAL PASS")
    print("SCOPE one born stress box only; G2 remains open")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
