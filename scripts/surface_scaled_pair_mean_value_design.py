"""Mean-value enclosure design for a scaled pair-sum beta box.

The ordinary bivariate Horner enclosure loses beta correlation.  This lane
evaluates the Taylor polynomial at the beta midpoint and encloses the beta
slope on the full box, then applies the one-dimensional mean-value theorem.
It remains a local design primitive until its cell driver is replayed.
"""

from __future__ import annotations

from fractions import Fraction

from flint import arb, ctx

from surface_scaled_pair_tail_derivative_design import (
    tail_beta_derivative_bound,
)
from surface_scaled_pair_taylor_design import evaluate, pair_taylor, aq
from surface_scaled_pair_taylor_remainder_design import remainder_majorant


def derivative_poly(poly):
    return [[(j + 1) * row[j + 1] for j in range(len(row) - 1)]
            for row in poly]


def mean_value_cell(beta_lo: Fraction, beta_hi: Fraction,
                    lambda_lo: Fraction, lambda_hi: Fraction,
                    *, modes=115, beta_order=50, lambda_order=50,
                    precision=500):
    ctx.prec = precision
    beta_mid = (beta_lo + beta_hi) / 2
    beta_radius = (beta_hi - beta_lo) / 2
    lambda_mid = (lambda_lo + lambda_hi) / 2
    lambda_radius = (lambda_hi - lambda_lo) / 2
    finite, mode_tail, polynomial = pair_taylor(
        beta_mid, beta_radius, lambda_mid, lambda_radius,
        modes=modes, beta_order=beta_order,
        lambda_order=lambda_order, precision=precision)
    derivative = derivative_poly(polynomial)
    centre = evaluate(polynomial, arb(0), aq(lambda_radius))
    slope = evaluate(derivative, aq(beta_radius), aq(lambda_radius))
    lambda_rem, beta_rem, lambda_beta_rem = remainder_majorant(
        beta_lo, beta_hi, lambda_mid, lambda_radius,
        modes=modes, beta_order=beta_order,
        lambda_order=lambda_order, precision=precision)
    beta_box = aq(beta_mid) + aq(beta_radius) * arb("0 +/- 1")
    tail_slope = tail_beta_derivative_bound(
        beta_box, aq(lambda_hi), modes)
    # The omitted beta Taylor terms of the slope are bounded by the same
    # (beta_order+1)-st derivative majorant, with the mean-value power reduced
    # by one.  The beta derivative of the lambda remainder is computed by the
    # product-rule majorant in ``remainder_majorant``; no heuristic constant
    # is used.
    slope_remainder = (arb(beta_order + 1) / aq(beta_radius)
                       * beta_rem + lambda_beta_rem)
    slope_abs = max(abs(slope.lower()), abs(slope.upper()))
    total_upper = (centre.upper() + mode_tail.upper() + lambda_rem.upper()
                   + aq(beta_radius) * (slope_abs + tail_slope.upper()
                                        + slope_remainder.upper()))
    return {
        "centre": centre,
        "mode_tail": mode_tail,
        "slope": slope,
        "tail_slope": tail_slope,
        "lambda_remainder": lambda_rem,
        "lambda_beta_remainder": lambda_beta_rem,
        "beta_remainder": beta_rem,
        "slope_remainder": slope_remainder,
        "total_upper": total_upper,
    }


if __name__ == "__main__":
    out = mean_value_cell(Fraction("101.8125"), Fraction("101.84375"),
                          Fraction("1.5"), Fraction("1.51"))
    for name, value in out.items():
        print(name, value.str(30) if hasattr(value, "str") else value)
    print("SCOPE DESIGN ONLY; no G2/G6 promotion")
