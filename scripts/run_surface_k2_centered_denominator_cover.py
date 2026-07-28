"""Diagnostic complete t-cover for the centered K2 denominator carrier."""

from __future__ import annotations

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


def row(index: int, boxes):
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
    return tlo, thi, floor


def main() -> int:
    ctx.prec = PREC
    boxes = list(regular.sealed.born_t_boxes())
    if len(boxes) != 158:
        raise AssertionError(f"sealed partition length drift: {len(boxes)}")
    print("K2 CENTERED DENOMINATOR COVER", "rows", len(boxes),
          "delta", DLO, DHI, "center", CENTER, "half_width", HALF_WIDTH,
          "grid", GRID, "arb_bits", PREC, flush=True)
    seen = []
    worst = None
    for index in range(len(boxes)):
        tlo, thi, floor = row(index, boxes)
        print("ROW", index, "t", tlo, thi, "uniform_kd_floor", floor,
              flush=True)
        seen.append(index)
        if not floor > 0:
            print("CENTERED DENOMINATOR COVER FAIL", "index", index,
                  "floor", floor, flush=True)
            return 1
        if worst is None or floor < worst[0]:
            worst = (floor, index)
    if seen != list(range(158)):
        raise AssertionError("row index contract is not exactly 0,...,157")
    print("CENTERED DENOMINATOR COVER PASS", "rows", len(seen),
          "worst_index", worst[1], "worst_floor", worst[0],
          "DIAGNOSTIC ONLY", flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
