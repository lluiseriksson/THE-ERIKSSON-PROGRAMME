"""Diagnostic centered-denominator carrier for the K2 R4 widening cell.

The output is deliberately not a certificate. It only tests whether
centering the delta series can produce a positive denominator floor after the
registered outer-domain coefficient radii are charged.
"""

from __future__ import annotations

from fractions import Fraction

from flint import arb, ctx

import surface_remainder_delta0_extension_probe as regular
import surface_remainder_delta0_outer_domain_v7 as outer


INDEX = 144
DLO = Fraction(9, 1000)
DHI = Fraction(1, 100)
CENTER = (DLO + DHI) / 2
HALF_WIDTH = (DHI - DLO) / 2
GRID = 192
PHYSICAL_INNER = Fraction(1181, 1000)
PREC = 140


def main() -> int:
    ctx.prec = PREC
    boxes = list(regular.sealed.born_t_boxes())
    tlo, thi = boxes[INDEX]
    expected = (Fraction(72, 25), Fraction(29, 10))
    if (tlo, thi) != expected:
        raise AssertionError(f"sealed t-box drift: {(tlo, thi)} != {expected}")

    t = regular.hull(regular.aq(tlo), regular.aq(thi))
    center = regular.aq(CENTER)
    nominal = regular.parallel_integrate_coefficients(center, t, GRID)
    outer_bounds = outer.outer_derivative_bounds_box_to(
        DLO, DHI, PHYSICAL_INNER)
    kd = nominal["kd"].coeffs()
    kd0_lower = arb(kd[0].lower()) - arb(outer_bounds["kd"][0].upper())
    variation = arb(0)
    h = regular.aq(HALF_WIDTH)
    for order in range(1, len(kd)):
        radius = arb(kd[order].abs_upper()) + arb(outer_bounds["kd"][order].upper())
        variation += radius * h**order
    floor = kd0_lower - variation
    print("K2 CENTERED DENOMINATOR PROBE")
    print("index", INDEX, "t", tlo, thi, "delta", DLO, DHI,
          "center", CENTER, "half_width", HALF_WIDTH,
          "grid", GRID, "arb_bits", PREC)
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


if __name__ == "__main__":
    raise SystemExit(main())
