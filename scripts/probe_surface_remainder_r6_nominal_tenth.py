"""Nominal R6 feasibility probe for the tenth K2 birth.

This is deliberately design-only.  It extends the regular ball polynomial to
the exact r6 head (delta^5 coefficient) while omitting companion/outer-tail
charges.  A positive result would justify building a fresh R6 production
contract; it cannot promote K2 or G2.
"""

from fractions import Fraction
import heapq

from flint import arb, arb_series, ctx

import surface_bessel_integral_remainder as bessel
import surface_remainder_delta0_extension_probe as regular
import surface_remainder_delta0_series_design as series
from surface_remainder_s2_direct_judge import closed_forms


def relative_polynomial_series5(h, family):
    out = arb_series([arb(0)], h.prec)
    for coefficient in reversed(bessel.relative_coefficients(family, 5)):
        out = out*h + regular.aq(coefficient)
    return out


def assemble_y_six(moments, t):
    bilinear = moments["kd"]*moments["hdf"] - moments["kf"]*moments["hdd"]
    coeffs = bilinear.coeffs() + [arb(0)]*8
    quotient = arb_series(coeffs[1:7], 6)
    return 4*quotient/moments["kd"]**2


def run_box(lo, hi, grid=32):
    ctx.prec = 120
    series.relative_polynomial_series = relative_polynomial_series5
    t = regular.hull(regular.aq(lo), regular.aq(hi))
    # The coefficient head is evaluated at the analytic endpoint delta=0;
    # an interval in the constant series term would make Arb reject division
    # by the root series even though the full integral has a removable limit.
    lane = arb(0)
    rows = regular.integrate_coefficients(t, grid=grid, side=12,
                                          prec=7, base=lane)
    moments = {name: arb_series(values, 7) for name, values in rows.items()}
    y = assemble_y_six(moments, t)
    c = (t/4).cos()
    r6 = (8148*c**12 + 17095*c**10 + 10768*c**8 + 634576*c**6
          -2557408*c**4 + 2283296*c**2 - 549376)/(131072*c**18)
    coeff5 = y.coeffs()[5]
    return lo, hi, coeff5, r6


def adaptive_box(lo, hi, max_cells=512, seed=8):
    """Dependency-focused nominal integration; design-only."""
    ctx.prec = 120
    series.relative_polynomial_series = relative_polynomial_series5
    t = regular.hull(regular.aq(lo), regular.aq(hi))
    side = arb(12)
    width = side/seed
    heap, serial = [], 0

    def evaluate(slo, shi, alo, ahi):
        values = regular.nominal_moment_series(
            arb(0), t, regular.hull(slo, shi), regular.hull(alo, ahi), 7)
        area = 4*(shi-slo)*(ahi-alo)
        return {name: value*area for name, value in values.items()}

    def push(slo, shi, alo, ahi):
        nonlocal serial
        values = evaluate(slo, shi, alo, ahi)
        score = sum(float(v.coeffs()[5].rad()) for v in values.values())
        heapq.heappush(heap, (-score, serial, slo, shi, alo, ahi, values))
        serial += 1

    for i in range(seed):
        for j in range(seed):
            push(width*i, width*(i+1), width*j, width*(j+1))
    while len(heap)+3 <= max_cells:
        _, _, slo, shi, alo, ahi, _ = heapq.heappop(heap)
        sm, am = (slo+shi)/2, (alo+ahi)/2
        push(slo, sm, alo, am); push(sm, shi, alo, am)
        push(slo, sm, am, ahi); push(sm, shi, am, ahi)
    totals = {name: [arb(0) for _ in range(7)]
              for name in ("kd", "kf", "hdd", "hdf")}
    for *_, values in heap:
        for name, value in values.items():
            for order, coefficient in enumerate(value.coeffs()):
                totals[name][order] += coefficient
    moments = {name: arb_series(value, 7) for name, value in totals.items()}
    y = assemble_y_six(moments, t)
    c = (t/4).cos()
    r6 = (8148*c**12 + 17095*c**10 + 10768*c**8 + 634576*c**6
          -2557408*c**4 + 2283296*c**2 - 549376)/(131072*c**18)
    return lo, hi, y.coeffs()[5], r6, len(heap)


def run(index=0, grid=32):
    boxes = list(regular.sealed.born_t_boxes())
    return run_box(*boxes[index], grid=grid)


if __name__ == "__main__":
    lo, hi, coeff5, r6 = run()
    print("R6 NOMINAL TENTH-BIRTH PROBE")
    print("t_box", lo, hi, "grid", 32)
    print("nominal_coefficient5", coeff5.str(30))
    print("exact_r6_head", r6.str(30))
    print("DESIGN ONLY; companion and outer-tail charges open")
