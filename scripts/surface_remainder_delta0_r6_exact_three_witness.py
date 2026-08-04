"""Exact-monomial R6 three-witness probe for the tenth birth.

The spatial integral is evaluated by the independent symbolic monomial
backend, avoiding rectangular-cell dependency.  This deliberately omits the
annulus and outer spatial-tail charge; it is therefore a design witness, not
K2/G2/G6 evidence.
"""

from flint import arb, arb_series, ctx

import probe_surface_remainder_r6_companion_charge as companion
import probe_surface_remainder_r6_exact_box_integral as exact
import surface_remainder_delta0_extension_probe as regular
import surface_remainder_delta0_r4_extension_010_hybrid_contract as contract
from surface_remainder_s2_direct_judge import closed_forms
from surface_remainder_delta0_fifth_coefficient import target_y4


TARGET = arb(7600)


def assemble(moments, t):
    bilinear = moments["kd"]*moments["hdf"] \
        - moments["kf"]*moments["hdd"]
    coefficients = bilinear.coeffs()+[arb(0)]*8
    quotient = arb_series(coefficients[1:7], 6)
    return 4*quotient/moments["kd"]**2


def witness(index, grid):
    boxes = list(regular.sealed.born_t_boxes())
    lo, hi = boxes[index]
    moments, c_box = companion.moment_series(lo, hi)
    y = assemble(moments, c_box*4)
    coeff5 = arb(y.coeffs()[5].abs_upper())
    charge, _, _, _, _ = companion.charge(lo, hi)
    margin = TARGET-coeff5-charge
    return lo, hi, coeff5, charge, margin


def main():
    ctx.prec = 140
    passed = True
    print("R6 EXACT-MONOMIAL THREE-WITNESS PROBE",
          "witnesses", contract.WITNESSES, flush=True)
    for index, grid in contract.WITNESSES:
        lo, hi, coeff5, charge, margin = witness(index, grid)
        lower = arb(margin.lower())
        print("TRY", index, grid, "t", lo, hi,
              "Y5", coeff5.str(24), "companion", charge.str(24),
              "margin_lower", lower.str(24), flush=True)
        passed = passed and lower > 0
    print("R6 EXACT-MONOMIAL THREE-WITNESS-PASS" if passed
          else "R6 EXACT-MONOMIAL THREE-WITNESS-FAIL", flush=True)
    print("DESIGN ONLY; annulus, outer-tail, and weighted S1'''/S2''' charges open",
          flush=True)
    return 0 if passed else 1


if __name__ == "__main__":
    raise SystemExit(main())
