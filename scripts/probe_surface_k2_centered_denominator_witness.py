"""Centered K2 denominator diagnostic for one sealed t-box witness."""

from __future__ import annotations

import argparse
from fractions import Fraction

from flint import arb, ctx

import surface_remainder_delta0_extension_probe as regular
import surface_remainder_delta0_outer_domain_v7 as outer


DLO = Fraction(9, 1000)
DHI = Fraction(1, 100)
CENTER = (DLO + DHI) / 2
HALF_WIDTH = (DHI - DLO) / 2
GRID = 192
PHYSICAL_INNER = Fraction(1181, 1000)
PREC = 140
WITNESSES = (0, 50, 100, 144, 156)


def run(index: int) -> int:
    ctx.prec = PREC
    boxes = list(regular.sealed.born_t_boxes())
    if index not in WITNESSES:
        raise ValueError(f"index {index} is not a preregistered witness")
    tlo, thi = boxes[index]
    t = regular.hull(regular.aq(tlo), regular.aq(thi))
    nominal = regular.parallel_integrate_coefficients(
        regular.aq(CENTER), t, GRID)
    outer_bounds = outer.outer_derivative_bounds_box_to(
        DLO, DHI, PHYSICAL_INNER)
    kd = nominal["kd"].coeffs()
    kd0_lower = arb(kd[0].lower()) - arb(outer_bounds["kd"][0].upper())
    h = regular.aq(HALF_WIDTH)
    variation = arb(0)
    for order in range(1, len(kd)):
        radius = arb(kd[order].abs_upper()) + arb(outer_bounds["kd"][order].upper())
        variation += radius * h**order
    floor = kd0_lower - variation
    print("K2 CENTERED DENOMINATOR WITNESS", index)
    print("t", tlo, thi, "delta", DLO, DHI, "center", CENTER,
          "half_width", HALF_WIDTH, "grid", GRID, "arb_bits", PREC)
    print("nominal_kd0_lower", kd[0].lower())
    print("outer_kd0_radius", outer_bounds["kd"][0].upper())
    print("centered_kd_floor", kd0_lower)
    print("variation_charge", variation)
    print("uniform_kd_floor", floor)
    if floor > 0:
        print("CENTERED DENOMINATOR PASS; DIAGNOSTIC ONLY")
        return 0
    print("CENTERED DENOMINATOR FAIL; DIAGNOSTIC ONLY")
    return 1


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--index", type=int, required=True)
    args = parser.parse_args()
    return run(args.index)


if __name__ == "__main__":
    raise SystemExit(main())
