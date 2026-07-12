"""Derive the candidate delta^5 coefficient of the regularized S2 carrier.

This is an exact symbolic design calculation.  It deliberately has no
pre-recorded target and emits no certification word; a separate immutable
checker will be made only after the expression has been independently
reduced and registered.
"""

import sympy as sp

from surface_bessel_integral_remainder import relative_coefficients


def derive_candidate(c_value=None):
    d, sigma, tau = sp.symbols("delta sigma tau", positive=True)
    c = (sp.symbols("c", positive=True) if c_value is None
         else sp.Rational(c_value))
    s2, t2 = sigma**2, tau**2
    retained = 7

    def trunc(expression):
        return sp.series(expression, d, 0, retained).removeO().expand()

    def sinc_square_scaled(x2):
        return trunc(sum(
            sp.Rational((-1)**n*2**(2*n+1), sp.factorial(2*n+2))
            *x2/4*(d*x2/4)**n for n in range(retained)))

    p, q = sinc_square_scaled(s2), sinc_square_scaled(t2)
    w_over = trunc(p+q-d*p*q/c**2)
    root = trunc(sp.sqrt(1-d*w_over))
    phase = trunc(-4*c*w_over/(1+root))
    phase0 = phase.subs(d, 0)
    exp_correction = trunc(sp.exp(phase-phase0))
    inv_z = trunc(d/(4*c*root))

    def companion(family):
        return trunc(sum(
            sp.Rational(value.numerator, value.denominator)*inv_z**order
            for order, value in enumerate(
                relative_coefficients(family, retained-1))))

    d_weight = trunc(2*(1-d*(p+q)))
    cc = 2*c**2-1
    f_over = trunc(-4*p*(
        -2*cc*p*d-cc*q*d+2*cc+2*p*q*d**2-p*d-2*q*d+1))
    kernel = trunc(root**sp.Rational(-3, 2)
                   *companion("A")*exp_correction)
    hregular = trunc(root**sp.Rational(-5, 2)
                     *companion("B")*exp_correction)
    integrands = {
        "KD": trunc(kernel*d_weight),
        "KF": trunc(kernel*f_over),
        "HDD": trunc(hregular*d_weight**2),
        "HDF": trunc(hregular*d_weight*f_over),
    }

    def gaussian_expectation(poly):
        total = 0
        for (i, j), coefficient in sp.Poly(
                sp.expand(poly), sigma, tau).terms():
            if i % 2 or j % 2:
                continue
            mi = sp.factorial2(i-1)/c**(i//2) if i else 1
            mj = sp.factorial2(j-1)/c**(j//2) if j else 1
            total += coefficient*mi*mj
        return sp.factor(total)

    moments = {
        name: [gaussian_expectation(value.coeff(d, order))
               for order in range(retained)]
        for name, value in integrands.items()
    }
    bilinear = [sp.factor(sum(
        moments["KD"][j]*moments["HDF"][n-j]
        -moments["KF"][j]*moments["HDD"][n-j]
        for j in range(n+1))) for n in range(retained)]
    bilinear_series = sum(d**n*bilinear[n]
                          for n in range(1, retained))
    kd_series = sum(d**n*moments["KD"][n]
                    for n in range(retained))
    y = sp.series(
        bilinear_series/(2*c*d*kd_series**2), d, 0, 6
    ).removeO().expand()
    return sp.factor(y.coeff(d, 5))


if __name__ == "__main__":
    print("DESIGN candidate Y delta coefficient 5 =", derive_candidate(),
          flush=True)
    print("DESIGN ONLY: independent reduction and target registration open",
          flush=True)
