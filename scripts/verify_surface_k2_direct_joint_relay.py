"""Exact algebra audit for the K2 direct joint-remainder relay.

The regular K2 certificate controls Y directly.  This audit records the
normalization Y = beta * X_main and the implication from the certified
Y-remainder to the main-saddle extraction bound.  It deliberately does not
identify that joint remainder with the older, separately named tail tau.
"""

from __future__ import annotations

from fractions import Fraction

import sympy as sp


DELTA_MAX = Fraction(9, 1000)
BETA_OLD = 15


def verify_symbolic_relay() -> None:
    beta, delta = sp.symbols("beta delta", nonzero=True)
    scale, quadrant = sp.symbols("scale quadrant", nonzero=True)
    z, c, i1, i2 = sp.symbols("z c I1 I2")
    mu_d, mu_f, nu_d, nu_f = sp.symbols(
        "mu_d mu_f nu_d nu_f", nonzero=True
    )
    leading, r2, remainder = sp.symbols("T r2 remainder")

    # Derive, rather than assume, the common scale used by
    # surface_remainder_y_carrier.py.  The original paper kernels are
    # K=I1(z)/R=2*beta*I1(z)/z and H_B=I2(z)/z^2.  The regular code stores
    # A=exp(-z)I1/z and B=exp(-z)I2/z^2, then multiplies their common phase
    # exp(z-4*beta*c).
    original_k = 2 * beta * i1 / z
    original_h = i2 / z**2
    code_k = (
        2 * beta ** sp.Rational(5, 2)
        * sp.exp(-z) * i1 / z
        * sp.exp(z - 4 * beta * c)
    )
    code_h = (
        beta ** sp.Rational(3, 2)
        * sp.exp(-z) * i2 / z**2
        * sp.exp(z - 4 * beta * c)
    )
    derived_scale = beta ** sp.Rational(3, 2) * sp.exp(-4 * beta * c)
    assert sp.simplify(code_k - derived_scale * original_k) == 0
    assert sp.simplify(code_h - derived_scale * original_h) == 0

    # Each regularized code moment has the same positive Bessel/exponential
    # scale.  A common quadrant multiplicity also cancels from the quotient.
    scale = derived_scale
    kd = quadrant * scale * mu_d
    kf = quadrant * scale * mu_f
    hdd = quadrant * scale * nu_d
    hdf = quadrant * scale * nu_f
    y_code = 4 * beta**4 * (kd * hdf - kf * hdd) / kd**2
    x_main = 4 * beta**3 * (mu_d * nu_f - mu_f * nu_d) / mu_d**2
    assert sp.simplify(y_code - beta * x_main) == 0

    # The certified statement is Y = T + r2*delta + remainder with
    # |remainder| <= Theta3*delta^2.  Since X_main = delta*Y, multiplying
    # by delta gives the joint remainder without splitting it into rho/tau.
    y_model = leading + r2 * delta + remainder
    x_from_y = delta * y_model
    joint_residual = x_from_y - leading * delta - r2 * delta**2
    assert sp.simplify(joint_residual - delta * remainder) == 0

    # beta=1/delta is the only parameter substitution used by the relay.
    assert sp.simplify((beta * x_main).subs(beta, 1 / delta) - x_main.subs(
        beta, 1 / delta
    ) / delta) == 0


def verify_budget_inclusion() -> None:
    # On the certified half-line delta <= 9/1000, the direct joint bound
    # yields |X_main-T*delta| <= (|r2|+Theta3*delta_max)*delta^2.
    # This is strictly sharper than even one old Theta3/beta_1 bucket, hence
    # also than the manuscript's conservative two-bucket R1.
    old_one_bucket = Fraction(1, BETA_OLD)
    old_two_buckets = Fraction(2, BETA_OLD)
    assert DELTA_MAX < old_one_bucket < old_two_buckets


def main() -> int:
    verify_symbolic_relay()
    verify_budget_inclusion()
    print("K2 DIRECT-JOINT RELAY ALGEBRA PASS")
    print("NORMALIZATION Y = beta*X_main PASS")
    print(
        "IMPLICATION |Y-T-r2*delta|<=Theta3*delta^2 "
        "=> |X_main-T*delta-r2*delta^2|<=Theta3*delta^3 PASS"
    )
    print("BUDGET 9/1000 < 1/15 < 2/15 PASS")
    print(
        "SCOPE replaces the old split-tail route; "
        "does not prove or identify a separate tau/H_tail"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
