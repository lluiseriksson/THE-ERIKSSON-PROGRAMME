"""Independent exact checker for the seventh and eighth K2 heads.

This engine deliberately uses SymPy's expression-level series expansion,
unlike the hand-written coefficient-list recurrences used by the design
derivation.  See the preregistration before running this expensive checker.
"""

from __future__ import annotations

import hashlib
from pathlib import Path
import platform
import subprocess

import sympy as sp

from surface_bessel_integral_remainder import relative_coefficients
from surface_remainder_delta0_fourth_coefficient import target_y3
from surface_remainder_delta0_fifth_coefficient import target_y4
from surface_remainder_delta0_sixth_coefficient import target_y5


RETAINED = 9


def target_y6(c):
    return (
        2085412*c**14 + 6775103*c**12 + 11636676*c**10
        - 52644752*c**8 + 1046587520*c**6 - 2880628992*c**4
        + 2254849024*c**2 - 513015808
    )/(33554432*c**21)


def target_y7(c):
    return (
        19936*c**16 + 119595*c**14 + 323054*c**12 + 637408*c**10
        - 12653880*c**8 + 104539328*c**6 - 219463616*c**4
        + 153352416*c**2 - 33064504
    )/(524288*c**24)


def frozen_targets(c):
    return [
        (4*c**2-1)/(8*c**3),
        (-8*c**4+15*c**2-4)/(32*c**6),
        (-12*c**6-485*c**4+796*c**2-224)/(1024*c**9),
        target_y3(c),
        target_y4(c),
        target_y5(c),
        target_y6(c),
        target_y7(c),
    ]


def derive_coefficients():
    delta, c, sigma, tau = sp.symbols(
        "delta c sigma tau", positive=True
    )
    sigma2, tau2 = sigma**2, tau**2

    def trunc(expression):
        return sp.series(
            expression, delta, 0, RETAINED
        ).removeO().expand()

    def sinc_square_scaled(x2):
        return trunc(sum(
            sp.Rational((-1)**n*2**(2*n+1), sp.factorial(2*n+2))
            * x2/4*(delta*x2/4)**n
            for n in range(RETAINED)
        ))

    p = sinc_square_scaled(sigma2)
    q = sinc_square_scaled(tau2)
    w = trunc(p+q-delta*p*q/c**2)
    root = trunc(sp.sqrt(1-delta*w))
    phase = trunc(-4*c*w/(1+root))
    phase0 = phase.subs(delta, 0)
    exponential = trunc(sp.exp(phase-phase0))
    h = trunc(delta/(4*c*root))

    def companion(family):
        return trunc(sum(
            sp.Rational(value.numerator, value.denominator)*h**order
            for order, value in enumerate(
                relative_coefficients(family, RETAINED-1)
            )
        ))

    d_weight = trunc(2*(1-delta*(p+q)))
    cc = 2*c**2-1
    f_weight = trunc(-4*p*(
        -2*cc*p*delta - cc*q*delta + 2*cc + 1
        + 2*p*q*delta**2 - p*delta - 2*q*delta
    ))
    kernel = trunc(
        root**sp.Rational(-3, 2)*companion("A")*exponential
    )
    hregular = trunc(
        root**sp.Rational(-5, 2)*companion("B")*exponential
    )
    integrands = {
        "KD": trunc(kernel*d_weight),
        "KF": trunc(kernel*f_weight),
        "HDD": trunc(hregular*d_weight**2),
        "HDF": trunc(hregular*d_weight*f_weight),
    }

    def gaussian_expectation(polynomial):
        total = sp.S.Zero
        for (i, j), coefficient in sp.Poly(
            sp.expand(polynomial), sigma, tau
        ).terms():
            if i % 2 or j % 2:
                continue
            mi = (
                sp.factorial2(i-1)/c**(i//2)
                if i else sp.S.One
            )
            mj = (
                sp.factorial2(j-1)/c**(j//2)
                if j else sp.S.One
            )
            total += coefficient*mi*mj
        return sp.cancel(total)

    moments = {
        name: [
            gaussian_expectation(value.coeff(delta, order))
            for order in range(RETAINED)
        ]
        for name, value in integrands.items()
    }
    bilinear = [
        sp.cancel(sum(
            moments["KD"][j]*moments["HDF"][order-j]
            - moments["KF"][j]*moments["HDD"][order-j]
            for j in range(order+1)
        ))
        for order in range(RETAINED)
    ]
    if sp.cancel(bilinear[0]) != 0:
        raise AssertionError("exact B(0) cancellation failed")
    bilinear_series = sum(
        delta**order*bilinear[order]
        for order in range(1, RETAINED)
    )
    kd_series = sum(
        delta**order*moments["KD"][order]
        for order in range(RETAINED)
    )
    carrier = sp.series(
        bilinear_series/(2*c*delta*kd_series**2),
        delta,
        0,
        RETAINED-1,
    ).removeO().expand()
    return [
        sp.factor(carrier.coeff(delta, order))
        for order in range(RETAINED-1)
    ]


def verify(coefficients=None):
    c = sp.symbols("c", positive=True)
    actual = derive_coefficients() if coefficients is None else coefficients
    targets = frozen_targets(c)
    if len(actual) != len(targets):
        raise AssertionError((len(actual), len(targets)))
    for order, (value, target) in enumerate(zip(actual, targets)):
        difference = sp.cancel(value-target)
        if difference != 0:
            raise AssertionError(
                f"Y{order} target mismatch: {difference}"
            )
    return [sp.factor(value) for value in actual]


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest().upper()


def main():
    path = Path(__file__).resolve()
    root = path.parents[1]
    prereg = (
        root/"docs"/
        "SURFACE-REMAINDER-R7-R8-EXACT-HEAD-PREREG-20260728.md"
    )
    dependency = root/"scripts"/"surface_bessel_integral_remainder.py"
    head = subprocess.check_output(
        ["git", "-c", "safe.directory=*", "rev-parse", "HEAD"],
        cwd=root,
        text=True,
    ).strip()
    print("R7/R8 INDEPENDENT EXACT-HEAD CHECKER", flush=True)
    print(f"git_head {head}", flush=True)
    print(f"python {platform.python_version()}", flush=True)
    print(f"sympy {sp.__version__}", flush=True)
    print(f"script_sha256 {digest(path)}", flush=True)
    print(f"prereg_sha256 {digest(prereg)}", flush=True)
    print(f"dependency_sha256 {digest(dependency)}", flush=True)
    values = verify()
    for order, value in enumerate(values):
        print(f"Y{order} {value}", flush=True)
    print("R7/R8 INDEPENDENT EXACT-HEAD CHECKER PASS", flush=True)
    print(
        "SCOPE exact fixed-square surrogate heads only; "
        "complex supremum, true companion, and exterior remain open",
        flush=True,
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
