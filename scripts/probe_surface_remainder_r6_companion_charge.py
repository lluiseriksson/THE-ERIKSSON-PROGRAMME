"""Design probe for the order-five Bessel-companion charge in K2/R6.

This is deliberately separate from the sealed order-four certificate.  It
uses the exact-monomial nominal moments and keeps the four companion error
coefficients separate; replacing all four by the largest one is needlessly
catastrophic near the tenth birth.
"""

from fractions import Fraction
import sympy as sp

from flint import arb, arb_series, ctx

import probe_surface_remainder_r6_exact_box_integral as exact
import surface_remainder_delta0_series_cover_design as sealed
from surface_remainder_companion_error_ordered import moment_error_coefficients


N = 7
DELTA_MAX = arb(1) / 100


def rat(value):
    return sp.Rational(value.numerator, value.denominator)


def moment_series(t_lo, t_hi):
    """Mirror the frozen exact integrator without changing its hash."""
    moment_terms = exact.frozen_terms()

    def aq_sympy(value):
        value = sp.Rational(value)
        return arb(str(value.p)) / arb(str(value.q))

    c_box = exact.hull((aq_sympy(t_lo) / 4).cos(),
                       (aq_sympy(t_hi) / 4).cos())

    def gaussian_moment(power):
        a = c_box / 2
        exponent = arb(power + 1) / 2
        upper = a * 12**2
        return a**(-exponent) * upper.gamma_lower(exponent) / 2

    moments = {}
    for name, values in moment_terms.items():
        rows = []
        for terms in values:
            total = arb(0)
            for i, j, numerator, denominator in terms:
                total += exact.eval_coefficients((numerator, denominator), c_box) \
                    * gaussian_moment(i) * gaussian_moment(j)
            rows.append(4 * total)
        moments[name] = arb_series(rows, N)
    return moments, c_box


def abs_series_bound(series):
    return sum((arb(coef).abs_upper() * DELTA_MAX**k
                for k, coef in enumerate(series.coeffs())), arb(0))


def charge(t_lo, t_hi):
    moments, c_box = moment_series(t_lo, t_hi)
    names = ("kd", "kf", "hdd", "hdf")
    bounds = {name: abs_series_bound(moments[name]) for name in names}
    dmin = arb(moments["kd"].coeffs()[0].lower())
    dmax = bounds["kd"]
    errors = moment_error_coefficients(5)
    e = {name: arb(getattr(errors, name).upper()) for name in names}

    # |Delta B| <= A delta^6, with the individual error coefficients kept.
    A = (e["kd"]*bounds["hdf"] + bounds["kd"]*e["hdf"]
         + e["kf"]*bounds["hdd"] + bounds["kf"]*e["hdd"]
         + e["kd"]*e["hdf"]*DELTA_MAX**6
         + e["kf"]*e["hdd"]*DELTA_MAX**6)
    actual = dmin - e["kd"]*DELTA_MAX**6
    if not actual > 0:
        raise ValueError("companion perturbation does not resolve KD")

    # Direct nominal bound for B/delta, rather than the crude 2*max(M)^2.
    bilinear = moments["kd"]*moments["hdf"] - moments["kf"]*moments["hdd"]
    bcoeff = bilinear.coeffs() + [arb(0)] * N
    b_over_delta = arb_series(bcoeff[1:N], N-1)
    bq = sum((arb(coef).abs_upper() * DELTA_MAX**k
              for k, coef in enumerate(b_over_delta.coeffs())), arb(0))

    first = 4*A/actual**2
    # The denominator perturbation is one extra delta and is charged at
    # delta_max when expressed in the R6 coefficient (the target is delta^5).
    invdiff = (e["kd"]*DELTA_MAX*(2*dmax + e["kd"]*DELTA_MAX**6)
               / (actual**2*dmin**2))
    second = 4*(bq + A*DELTA_MAX**5)*invdiff
    return first + second, A, bq, dmin, c_box


def main():
    ctx.prec = 140
    boxes = list(sealed.born_t_boxes())
    worst = None
    for index, (lo, hi) in enumerate(boxes):
        value, a, bq, kd, c = charge(rat(lo), rat(hi))
        if worst is None or value > worst[0]:
            worst = (value, index, a, bq, kd, c)
        print("ROW", index, "charge", value.str(18), "A", a.str(14),
              "B_over_delta", bq.str(14), "KD0", kd.str(14), flush=True)
    print("R6 COMPANION CHARGE DESIGN", flush=True)
    print("ROWS", len(boxes), "WORST", worst[1], worst[0].str(30), flush=True)
    print("TARGET_LEFT_AFTER_NOMINAL", (arb(7600)-arb("2145.3549728393555")).str(20), flush=True)
    print("DESIGN ONLY; completion, outer-tail, and weighted S1'''/S2''' open", flush=True)


if __name__ == "__main__":
    main()
