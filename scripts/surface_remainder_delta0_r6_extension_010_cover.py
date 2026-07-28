"""Three-witness R6 design probe for the tenth K2 regular birth.

This file is deliberately byte-separate from the manifested R4 chain.  It
uses seventh-order nominal moments, the split outer-domain wrapper,
and a componentwise order-five companion charge.  No gate is promoted here.
"""

from concurrent.futures import ProcessPoolExecutor
from fractions import Fraction

from flint import arb, arb_series, ctx

import surface_remainder_delta0_extension_probe as regular
import surface_remainder_delta0_outer_domain_r6split as outer
import surface_remainder_delta0_r4_extension_010_hybrid_contract as contract
from surface_remainder_companion_error_ordered import moment_error_coefficients
from surface_remainder_delta0_fifth_coefficient import target_y4
from surface_remainder_s2_direct_judge import closed_forms


PREC = 7
PHYSICAL_INNER = Fraction(1181, 1000)
TARGET = arb(7600)


def _wire(value):
    return value.lower().str(90), value.upper().str(90)


def _unwire(value):
    return regular.hull(arb(value[0]), arb(value[1]))


def _row_slice(arguments):
    precision, base_wire, t_wire, grid, start, stop = arguments
    ctx.prec = precision
    base, t = _unwire(base_wire), _unwire(t_wire)
    totals = {name: [arb(0) for _ in range(PREC)]
              for name in ("kd", "kf", "hdd", "hdf")}
    width = arb(12) / grid
    for i in range(start, stop):
        for j in range(grid):
            sigma = regular.hull(width*i, width*(i+1))
            tau = regular.hull(width*j, width*(j+1))
            values = regular.nominal_moment_series(
                base, t, sigma, tau, PREC)
            area = 4*width**2
            for name, series in values.items():
                for order, value in enumerate(series.coeffs()):
                    totals[name][order] += area*value
    return {name: [_wire(value) for value in row]
            for name, row in totals.items()}


def integrate_r6(base, t, grid, workers=4):
    if grid % workers:
        raise ValueError("grid must divide worker count")
    step = grid//workers
    args = [(ctx.prec, _wire(base), _wire(t), grid,
             k*step, (k+1)*step) for k in range(workers)]
    with ProcessPoolExecutor(max_workers=workers) as pool:
        pieces = list(pool.map(_row_slice, args))
    totals = {name: [arb(0) for _ in range(PREC)]
              for name in ("kd", "kf", "hdd", "hdf")}
    for piece in pieces:
        for name, row in piece.items():
            for order, value in enumerate(row):
                totals[name][order] += _unwire(value)
    return {name: arb_series(row, PREC) for name, row in totals.items()}


def assemble_y_six(moments, t):
    bilinear = moments["kd"]*moments["hdf"] - moments["kf"]*moments["hdd"]
    coeffs = bilinear.coeffs()+[arb(0)]*8
    quotient = arb_series(coeffs[1:7], 6)
    return 4*quotient/moments["kd"]**2


def componentwise_value_charge(delta_max, kd_lower, moment_abs, bands):
    """Convert mixed band/order-five errors to a conservative delta^5 charge."""
    companion = moment_error_coefficients(5)
    errors = {
        name: arb(bands[name].upper())
        + arb(getattr(companion, name).upper())*arb(delta_max.numerator)
        / arb(delta_max.denominator)
        for name in ("kd", "kf", "hdd", "hdf")
    }
    return outer.normalized_y_error_from_moment_coefficients(
        delta_max, kd_lower, moment_abs, errors)


def judge_t(lo, hi, grid):
    delta_max = Fraction(1, 100)
    t = regular.hull(regular.aq(lo), regular.aq(hi))
    coefficient5 = arb(0)
    kd_lower = None
    moment_abs = {name: arb(0) for name in ("kd", "kf", "hdd", "hdf")}
    core_sources = {}
    for dlo, dhi in contract.CORE_BOXES:
        lane = regular.hull(regular.aq(dlo), regular.aq(dhi))
        source = integrate_r6(lane, t, grid)
        core_sources[(dlo, dhi)] = source
        moments = outer.add_outer_derivatives_box_to_t(
            source, dlo, dhi, PHYSICAL_INNER, lo, hi)
        y = assemble_y_six(moments, t)
        coefficient5 = max(coefficient5,
                           arb(y.coeffs()[5].abs_upper()))
        lower = arb(moments["kd"].coeffs()[0].lower())
        kd_lower = lower if kd_lower is None else min(kd_lower, lower)
        for name, value in moments.items():
            moment_abs[name] = max(
                moment_abs[name], arb(value.coeffs()[0].abs_upper()))
    for dlo, dhi in contract.ANNULUS_BOXES:
        source = None
        for index, (_, core_hi) in enumerate(contract.CORE_BOXES):
            if dhi <= core_hi:
                source = core_sources[contract.CORE_BOXES[index]]
                break
        moments = outer.add_outer_derivatives_box_to_t(
            source, dlo, dhi, PHYSICAL_INNER, lo, hi)
        y = assemble_y_six(moments, t)
        coefficient5 = max(coefficient5,
                           arb(y.coeffs()[5].abs_upper()))
        lower = arb(moments["kd"].coeffs()[0].lower())
        kd_lower = lower if kd_lower is None else min(kd_lower, lower)
        for name, value in moments.items():
            moment_abs[name] = max(
                moment_abs[name], arb(value.coeffs()[0].abs_upper()))
    lane = regular.hull(arb(0), regular.aq(delta_max))
    _, _, r3, _ = closed_forms(t)
    r4 = target_y4((t/4).cos())
    # r5 is target_y4; the next coefficient is the bounded y[5].
    head = arb((r3 + r4*lane).abs_upper())
    radius, bands = outer.direct_moving_band_value_coefficients_from(
        delta_max, PHYSICAL_INNER, t.upper())
    value = componentwise_value_charge(
        delta_max, kd_lower, moment_abs, bands)
    delta = regular.aq(delta_max)
    margin = TARGET - coefficient5 - value
    return radius, head, coefficient5, value, margin


def main():
    ctx.prec = 140
    boxes = list(regular.sealed.born_t_boxes())
    print("R6 010 THREE-WITNESS SPLIT PROBE", "witnesses",
          contract.WITNESSES, flush=True)
    passed = True
    for index, grid in contract.WITNESSES:
        lo, hi = boxes[index]
        try:
            radius, head, coeff5, value, margin = judge_t(lo, hi, grid)
        except (ValueError, ZeroDivisionError) as exc:
            print("TRY", index, grid, "UNRESOLVED", type(exc).__name__,
                  str(exc), flush=True)
            passed = False
            continue
        lower = arb(margin.lower())
        print("TRY", index, grid, "radius", radius, "head", head,
              "Y5", coeff5, "value", value, "margin_lower", lower,
              flush=True)
        passed = passed and lower > 0
    print("R6 010 THREE-WITNESS-PASS" if passed
          else "R6 010 THREE-WITNESS-FAIL", flush=True)
    return 0 if passed else 1


if __name__ == "__main__":
    raise SystemExit(main())
