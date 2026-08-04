"""Centered direct-evaluation diagnostic for one K2 R3 cell."""

from __future__ import annotations

import hashlib
import platform
import subprocess
from fractions import Fraction
from pathlib import Path

from flint import arb, arb_series, ctx

import surface_remainder_delta0_extension_probe as regular
import surface_remainder_delta0_outer_domain_v7 as outer
from surface_remainder_s2_direct_judge import closed_forms


INDEX = 144
DLO = Fraction(9, 1000)
DHI = Fraction(1, 100)
CENTER = Fraction(19, 2000)
HALF_WIDTH = Fraction(1, 2000)
GRID = 192
PHYSICAL_INNER = Fraction(1181, 1000)
PREC = 6
ARB_BITS = 140


def provenance():
    root = Path(__file__).resolve().parents[1]
    try:
        head = subprocess.check_output(
            ["git", "rev-parse", "HEAD"], cwd=root, text=True,
            stderr=subprocess.DEVNULL).strip()
    except Exception:
        head = "UNAVAILABLE"
    return hashlib.sha256(Path(__file__).read_bytes()).hexdigest(), head, platform.python_version()


def evaluate(series, x):
    value = arb(0)
    for coefficient in reversed(series.coeffs()):
        value = value*x + coefficient
    return value


def main() -> int:
    ctx.prec = ARB_BITS
    boxes = list(regular.sealed.born_t_boxes())
    lo, hi = boxes[INDEX]
    if (lo, hi) != (Fraction(72, 25), Fraction(29, 10)):
        raise AssertionError("sealed t-box drift")
    t = regular.hull(regular.aq(lo), regular.aq(hi))
    center = regular.aq(CENTER)
    source = regular.parallel_integrate_coefficients(center, t, GRID)
    outer_bounds = outer.outer_derivative_bounds_box_to(
        DLO, DHI, PHYSICAL_INNER)
    moments = {}
    for name in source:
        nominal = source[name].coeffs()
        radius = outer_bounds[name]
        moments[name] = arb_series(
            [nominal[k] + radius[k]*arb("0 +/- 1") for k in range(PREC)],
            PREC)
    d = arb_series([center, arb(1)], PREC)
    bilinear = moments["kd"]*moments["hdf"] - moments["kf"]*moments["hdd"]
    y = 4*(bilinear/d)/moments["kd"]**2
    x = regular.hull(-regular.aq(HALF_WIDTH), regular.aq(HALF_WIDTH))
    y_box = evaluate(y, x)
    leading, r2, _, theta = closed_forms(t)
    delta = center+x
    model = leading+r2*delta
    residual = arb((y_box-model).abs_upper())
    budget = theta*regular.aq(DLO)**2
    margin = budget-residual
    tail_proxy = arb(y.coeffs()[-1].abs_upper())*regular.aq(HALF_WIDTH)**5
    script_hash, head, python = provenance()
    print("K2 CENTERED DIRECT EVAL", "index", INDEX, "t", lo, hi,
          "delta", DLO, DHI, "center", CENTER, "grid", GRID,
          "arb_bits", ARB_BITS)
    print("PROVENANCE script_sha256", script_hash)
    print("PROVENANCE git_head", head)
    print("PROVENANCE python", python)
    print("KD_center_lower", moments["kd"].coeffs()[0].lower())
    print("Y_box", y_box)
    print("residual_abs", residual)
    print("budget_min", budget)
    print("raw_margin_lower", arb(margin.lower()))
    print("truncation_tail_proxy_uncharged", tail_proxy)
    print("BESSEL_COMPANION_TAIL unresolved; NO R3 PROMOTION")
    if arb(margin.lower()) > 0:
        print("CENTERED DIRECT EVAL RAW PASS; DIAGNOSTIC ONLY")
        return 0
    print("CENTERED DIRECT EVAL RAW FAIL; SINGLE CELL TERMINAL")
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
