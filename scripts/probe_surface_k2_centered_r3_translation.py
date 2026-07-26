"""Single-cell R3 diagnostic using centered-to-absolute delta translation."""

from __future__ import annotations

import argparse
import hashlib
import platform
import subprocess
from fractions import Fraction
from math import comb
from pathlib import Path

from flint import arb, arb_series, ctx

import surface_remainder_delta0_extension_probe as regular
import surface_remainder_delta0_outer_domain_v7 as outer
from surface_remainder_delta0_companion_error import moment_error_coefficients
from surface_remainder_delta0_fourth_coefficient import target_y3
from surface_remainder_delta0_r4_extension_probe import assemble_y_through_four
from surface_remainder_s2_direct_judge import closed_forms


INDEX = 144
DLO = Fraction(9, 1000)
DHI = Fraction(1, 100)
CENTER = Fraction(19, 2000)
GRID = 192
PHYSICAL_INNER = Fraction(1181, 1000)
PREC = 6
ARB_BITS = 140


def provenance() -> dict[str, str]:
    root = Path(__file__).resolve().parents[1]
    try:
        head = subprocess.check_output(
            ["git", "rev-parse", "HEAD"], cwd=root, text=True,
            stderr=subprocess.DEVNULL).strip()
    except Exception:
        head = "UNAVAILABLE"
    return {
        "script_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "git_head": head,
        "python": platform.python_version(),
    }


def translated(values, center: arb):
    """Translate a degree-PREC jet in x to the absolute delta jet."""
    out = []
    for k in range(PREC):
        value = arb(0)
        for j in range(k, PREC):
            value += values[j] * comb(j, k) * (-center)**(j-k)
        out.append(value)
    return out


def translated_radius(values, center: arb):
    out = []
    for k in range(PREC):
        value = arb(0)
        for j in range(k, PREC):
            value += values[j] * comb(j, k) * abs(center)**(j-k)
        out.append(value)
    return out


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--index", type=int, default=INDEX)
    args = parser.parse_args()
    if args.index != INDEX:
        raise ValueError("only preregistered index 144 is admissible")
    ctx.prec = ARB_BITS
    boxes = list(regular.sealed.born_t_boxes())
    lo, hi = boxes[INDEX]
    if (lo, hi) != (Fraction(72, 25), Fraction(29, 10)):
        raise AssertionError("sealed t-box drift")
    t = regular.hull(regular.aq(lo), regular.aq(hi))
    center = regular.aq(CENTER)
    source = regular.parallel_integrate_coefficients(center, t, 192)
    annulus = tuple((Fraction(j, 1000), Fraction(j+1, 1000))
                    for j in range(9, 10))
    coefficient4 = arb(0)
    kd_lower = None
    moment_abs = {name: arb(0) for name in ("kd", "kf", "hdd", "hdf")}
    for dlo, dhi in annulus:
        outer_bounds = outer.outer_derivative_bounds_box_to(
            dlo, dhi, PHYSICAL_INNER)
        moments = {}
        for name in source:
            nominal = translated(source[name].coeffs(), center)
            radius = translated_radius(outer_bounds[name], center)
            moments[name] = arb_series(
                [nominal[k] + radius[k]*arb("0 +/- 1") for k in range(PREC)],
                PREC)
        lower = arb(moments["kd"].coeffs()[0].lower())
        kd_lower = lower if kd_lower is None else min(kd_lower, lower)
        y = assemble_y_through_four(moments, t)
        coefficient4 = max(coefficient4,
                           arb((y.coeffs()+[arb(0)]*5)[4].abs_upper()))
        for name, value in moments.items():
            moment_abs[name] = max(
                moment_abs[name], arb(value.coeffs()[0].abs_upper()))
    lane = regular.hull(arb(0), regular.aq(DHI))
    _, _, r3, theta = closed_forms(t)
    head = arb((r3+target_y3((t/4).cos())*lane).abs_upper())
    radius, bands = outer.direct_moving_band_value_coefficients_from(
        DHI, PHYSICAL_INNER)
    companion = moment_error_coefficients().__dict__
    errors = {name: bands[name]+companion[name] for name in bands}
    value = outer.normalized_y_error_from_moment_coefficients(
        DHI, kd_lower, moment_abs, errors)
    delta = regular.aq(DHI)
    margin = theta-head-(coefficient4+value)*delta**2
    print("K2 CENTERED R3 TRANSLATION", "index", INDEX, "t", lo, hi,
          "delta", DLO, DHI, "center", CENTER, "grid", GRID,
          "arb_bits", ARB_BITS)
    for key, value0 in provenance().items():
        print("PROVENANCE", key, value0)
    print("kd_lower", kd_lower)
    print("radius", radius, "Y4", coefficient4, "C_value", value)
    print("margin_lower", arb(margin.lower()))
    if arb(margin.lower()) > 0:
        print("CENTERED R3 TRANSLATION PASS; SINGLE CELL ONLY")
        return 0
    print("CENTERED R3 TRANSLATION FAIL; SINGLE CELL TERMINAL")
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
