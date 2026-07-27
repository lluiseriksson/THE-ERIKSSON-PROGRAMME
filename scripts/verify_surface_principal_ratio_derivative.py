"""Algebraic audit for the principal-moment ratio derivative.

The script identifies the exact scalar that a future interval certificate
must prove negative.  It does not assert that the covariance has a sign.
"""

from __future__ import annotations

import sympy as sp


def identities() -> dict[str, sp.Expr]:
    p, q, parameter, beta = sp.symbols(
        "P Q q beta", real=True, positive=True
    )
    c = sp.symbols("C", real=True)
    a0 = (1 - p) * (1 - q)
    b0 = p * q
    d = 2 * (1 - p - q)
    radius2 = 4 * (
        parameter**2 * a0 + (1 - parameter**2) * b0
    )
    log_radius_derivative = sp.cancel(
        sp.diff(radius2, parameter) / (2 * radius2)
    )
    assert sp.cancel(log_radius_derivative - 2 * parameter * d / radius2) == 0

    cos_s = 1 - 2 * p
    cos_alpha = 1 - 2 * q
    cos_2s = 1 - 8 * p + 8 * p**2
    n = c * cos_2s + cos_alpha * (
        c * cos_s - 1 + cos_s**2
    )
    f_point = sp.expand(n - c * d)
    j = sp.factor(sp.diff(f_point, c))
    assert sp.expand(j - 4 * p * (2 * p + q - 2)) == 0
    assert sp.diff(c, parameter) == 0
    f_parameter_derivative = sp.factor(
        sp.diff(f_point.subs(c, 2 * parameter**2 - 1), parameter)
    )
    assert sp.expand(
        f_parameter_derivative
        - 16 * parameter * p * (2 * p + q - 2)
    ) == 0

    # I1'(z)=I0(z)-I1(z)/z and I0(z)-I2(z)=2 I1(z)/z imply
    # z I1'(z)/I1(z)-1 = z I2(z)/I1(z).  Verify the substitution
    # algebra with formal Bessel values.
    z, i0, i1, i2 = sp.symbols("z I0 I1 I2", nonzero=True)
    i1prime = i0 - i1 / z
    recurrence = {i0: i2 + 2 * i1 / z}
    bessel_score = sp.simplify(
        (z * i1prime / i1 - 1).subs(recurrence)
    )
    assert sp.simplify(bessel_score - z * i2 / i1) == 0

    # Convert the covariance exactly to the main bilinear carrier.
    # H/K = I2/(4 beta^2 R I1), whereas the score is
    # 4 beta q D I2/(R I1) = 16 beta^3 q D H/K.
    radius, hkernel, kernel = sp.symbols("R H_B K", nonzero=True)
    score = 4 * beta * parameter * d * i2 / (radius * i1)
    h_over_k = i2 / (4 * beta**2 * radius * i1)
    assert sp.simplify(score - 16 * beta**3 * parameter * d * h_over_k) == 0
    am, fm, um, wm = sp.symbols("a f u w", nonzero=True)
    xmain = 4 * beta**3 * (am * wm - fm * um) / am**2
    covariance = 16 * beta**3 * parameter * (
        wm / am - (fm / am) * (um / am)
    )
    assert sp.simplify(covariance - 4 * parameter * xmain) == 0

    # Symmetry turns the explicit derivative term into 4q(Q_main-1).
    phi_sym = 2 - 6 * (p + q) + 4 * (p**2 + q**2 + p * q)
    loss_p = p * (2 - 2 * p - q)
    loss_q = q * (2 - 2 * q - p)
    assert sp.expand(d - phi_sym - 2 * (loss_p + loss_q)) == 0

    qmain, xscalar = sp.symbols("Q_main X")
    derivative_reduced = 4 * parameter * (xscalar + qmain - 1)

    return {
        "D": d,
        "R2": radius2,
        "dlogR_dq": log_radius_derivative,
        "F": sp.factor(f_point),
        "dF_dC": j,
        "dF_dq": f_parameter_derivative,
        "bessel_score_factor": bessel_score,
        "score": score,
        "covariance": covariance,
        "loss_identity": sp.expand(d - phi_sym),
        "derivative_reduced": derivative_reduced,
    }


def main() -> int:
    result = identities()
    print("PRINCIPAL RATIO DERIVATIVE ALGEBRA PASS")
    for name, value in result.items():
        print(name, "=", value)
    print(
        "EXACT PROBABILITY FORM: r'(q) = "
        "E_q[dF_dq/D] + Cov_q(F/D, dlogK_dq)"
    )
    print(
        "dlogK_dq = (z I2(z)/I1(z))*2*q*D/R^2; "
        "the covariance sign is not assumed"
    )
    print(
        "CANCELLATION: Cov_q(F/D,dlogK_dq)=4*q*X(q), hence "
        "r'(q)=4*q*(X(q)+Q_main(q)-1)"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
