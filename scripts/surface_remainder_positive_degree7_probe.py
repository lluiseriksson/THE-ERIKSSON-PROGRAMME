"""Grid-8 degree-seven probe on one full positive K2 birth."""

import argparse

from flint import arb, ctx

import surface_remainder_companion_error_ordered as companion
import surface_remainder_positive_t7_parallel as engine
import surface_remainder_positive_t_centered as algebra


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--t-lo", default="1.0")
    parser.add_argument("--t-hi", default="1.02")
    args = parser.parse_args()
    ctx.prec = 120
    dlo, dhi = arb("0.049"), arb("0.05")
    dc, dr = (dlo+dhi)/2, (dhi-dlo)/2
    tlo, thi = arb(args.t_lo), arb(args.t_hi)
    tc, tr = (tlo+thi)/2, (thi-tlo)/2
    db, tb = engine.physical.hull(dlo, dhi), engine.physical.hull(tlo, thi)
    perturbation = engine.physical.hull(-dr, dr)

    dm, _, dq = engine.moments(db, tb, grid=8)
    dseries, _ = engine.residual(dm, db, tb, arb(0))
    delta_tail = arb(dseries[6].v.abs_upper())*dr**6
    original = algebra.uncalibrated_moments(dm, dq)
    values = {name: series[0].v for name, series in original.items()}
    kd = arb(values["KD"].lower())
    magnitude = max(arb(value.abs_upper()) for value in values.values())
    if not kd > 0:
        print("DEGREE7 PROBE FAIL KD", kd); return 1
    cc = companion.normalized_y_error_coefficient(dhi, kd, magnitude, 6)
    companion_charge = cc*dhi**6

    bm, _, _ = engine.moments(dc, tb, grid=8)
    _, box = engine.residual(bm, dc, tb, perturbation)
    cm, _, _ = engine.moments(dc, tc, grid=8)
    _, center = engine.residual(cm, dc, tc, perturbation)
    nominal = algebra.taylor4_value_enclosure(center, box, tr)
    total = arb(nominal.abs_upper())+delta_tail+companion_charge
    budget = arb(150000)*dlo**6
    print("DEGREE7 GRID8 t", tlo, thi, "nominal", nominal.abs_upper(),
          "delta_tail", delta_tail, "companion", companion_charge,
          "total", total, "budget", budget, "margin", budget-total)
    print("DEGREE7 PROBE", "PASS" if total < budget else "FAIL")
    return 0 if total < budget else 1


if __name__ == "__main__":
    raise SystemExit(main())
