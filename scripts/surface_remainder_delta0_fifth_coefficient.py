"""Exact fifth coefficient of the regularized S2 carrier."""

import hashlib
from pathlib import Path
import platform
import subprocess

import sympy as sp

from surface_bessel_integral_remainder import relative_coefficients


def target_y4(c):
    return ((12940*c**10+16077*c**8+173288*c**6-1300912*c**4
             +1358400*c**2-346112)/(262144*c**15))


def derive():
    d, c, sigma, tau = sp.symbols(
        "delta c sigma tau", positive=True)
    s2, t2 = sigma**2, tau**2

    def trunc(expression):
        return sp.series(expression, d, 0, 6).removeO().expand()

    def sinc_square_scaled(x2):
        return trunc(sum(
            sp.Rational((-1)**n*2**(2*n+1), sp.factorial(2*n+2))
            *x2/4*(d*x2/4)**n for n in range(6)))

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
                relative_coefficients(family, 5))))

    a_relative, b_relative = companion("A"), companion("B")
    d_weight = trunc(2*(1-d*(p+q)))
    cc = 2*c**2-1
    f_over = trunc(-4*p*(
        -2*cc*p*d-cc*q*d+2*cc+2*p*q*d**2-p*d-2*q*d+1))
    kernel = trunc(root**sp.Rational(-3, 2)
                   *a_relative*exp_correction)
    hregular = trunc(root**sp.Rational(-5, 2)
                     *b_relative*exp_correction)
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
               for order in range(6)]
        for name, value in integrands.items()
    }
    kd, kf = moments["KD"], moments["KF"]
    hdd, hdf = moments["HDD"], moments["HDF"]
    bilinear = [sp.factor(sum(
        kd[j]*hdf[n-j]-kf[j]*hdd[n-j] for j in range(n+1)))
        for n in range(6)]
    bilinear_series = sum(d**n*bilinear[n] for n in range(1, 6))
    kd_series = sum(d**n*kd[n] for n in range(6))
    y = sp.series(
        bilinear_series/(2*c*d*kd_series**2), d, 0, 5
    ).removeO().expand()
    coefficient = sp.factor(y.coeff(d, 4))
    assert sp.simplify(coefficient-target_y4(c)) == 0
    return coefficient


def check():
    path = Path(__file__).resolve()
    root = path.parents[1]
    head = subprocess.check_output(
        ["git", "rev-parse", "HEAD"], cwd=root, text=True).strip()
    print("PROVENANCE script=scripts/"+path.name, flush=True)
    print("PROVENANCE script_sha256="
          +hashlib.sha256(path.read_bytes()).hexdigest(), flush=True)
    print("PROVENANCE git_head="+head, flush=True)
    print("PROVENANCE python="+platform.python_version(), flush=True)
    print("PROVENANCE sympy="+sp.__version__, flush=True)
    print("Y delta coefficient 4 =", derive(), flush=True)
    print("TARGET MATCH: fifth coefficient r5(c)", flush=True)


if __name__ == "__main__":
    check()
