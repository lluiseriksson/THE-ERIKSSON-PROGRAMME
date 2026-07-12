"""Grid-8 probe of the separately calibrated positive K2 bilinear."""

from flint import arb, ctx

import surface_remainder_companion_error_ordered as companion
import surface_remainder_positive_dual_parallel as engine
import surface_remainder_positive_t_centered as algebra


def original_moments(moments, qs):
    qk, qh = ([engine.tjet(x) for x in row] for row in qs)
    out = dict(moments)
    out["KF"] = algebra._sadd(moments["KF"], algebra._smul(qk, moments["KD"]))
    out["HDF"] = algebra._sadd(moments["HDF"], algebra._smul(qh, moments["HDD"]))
    return out


def main():
    ctx.prec = 120
    dlo, dhi, tlo, thi = map(arb, ("0.049", "0.05", "1.0", "1.02"))
    dc, dr, tc, tr = (dlo+dhi)/2, (dhi-dlo)/2, (tlo+thi)/2, (thi-tlo)/2
    db, tb = engine.p5.hull(dlo, dhi), engine.p5.hull(tlo, thi)
    perturbation = engine.p5.hull(-dr, dr)
    dm, _, dqs = engine.moments(db, tb)
    dseries, _ = engine.residual(dm, db, tb, arb(0), dqs)
    delta_tail = arb(dseries[6].v.abs_upper())*dr**6
    original = original_moments(dm, dqs)
    values = {name: row[0].v for name, row in original.items()}
    kd = arb(values["KD"].lower())
    magnitude = max(arb(x.abs_upper()) for x in values.values())
    if not kd > 0:
        print("DUAL PROBE FAIL KD", kd); return 1
    charge = companion.normalized_y_error_coefficient(
        dhi, kd, magnitude, 6)*dhi**6
    bm, _, bqs = engine.moments(dc, tb)
    _, box = engine.residual(bm, dc, tb, perturbation, bqs)
    cm, _, cqs = engine.moments(dc, tc)
    _, center = engine.residual(cm, dc, tc, perturbation, cqs)
    nominal = algebra.taylor4_value_enclosure(center, box, tr)
    total = arb(nominal.abs_upper())+delta_tail+charge
    budget = arb(150000)*dlo**6
    print("DUAL GRID8 nominal", nominal.abs_upper(), "delta_tail", delta_tail,
          "companion", charge, "total", total, "budget", budget,
          "margin", budget-total)
    print("DUAL PROBE", "PASS" if total < budget else "FAIL")
    return 0 if total < budget else 1


if __name__ == "__main__":
    raise SystemExit(main())
