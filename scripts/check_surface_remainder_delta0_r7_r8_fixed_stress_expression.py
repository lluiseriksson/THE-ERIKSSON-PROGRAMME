"""Independent exact expression-series check of R7/R8 near t=2.9.

This checker intentionally does not import the sparse coefficient-list
engine.  It builds ordinary SymPy expressions, truncates them with
``sympy.series``, and compares the resulting pointwise coefficients with the
frozen targets at one exact rational value of c close to cos(29/40).
"""

from __future__ import annotations

import hashlib
from pathlib import Path
import platform
import subprocess
import sys

import sympy as sp

SCRIPTS = Path(__file__).resolve().parent
if str(SCRIPTS) not in sys.path:
    sys.path.insert(0, str(SCRIPTS))

from surface_bessel_relative_coefficients_exact import relative_coefficients
from surface_remainder_delta0_exact_targets import frozen_targets


CSTAR = sp.Rational(
    7484994219661651049780560241386956279152584601396431,
    10**52,
)
RETAINED = 9


def cosine_partial_sum(x: sp.Rational, last: int) -> sp.Rational:
    return sp.factor(sum(
        sp.Rational((-1)**k, sp.factorial(2*k))*x**(2*k)
        for k in range(last+1)
    ))


def derive_at_fixed_c() -> list[sp.Expr]:
    d, sigma, tau = sp.symbols("delta sigma tau")
    c = CSTAR
    s2, t2 = sigma**2, tau**2

    def trunc(expression):
        return sp.series(
            expression, d, 0, RETAINED
        ).removeO().expand()

    def sinc_square_scaled(x2):
        return trunc(sum(
            sp.Rational((-1)**n*2**(2*n+1), sp.factorial(2*n+2))
            * x2/4 * (d*x2/4)**n
            for n in range(RETAINED)
        ))

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
                relative_coefficients(family, RETAINED-1)
            )
        ))

    d_weight = trunc(2*(1-d*(p+q)))
    cc = 2*c**2-1
    f_over = trunc(-4*p*(
        -2*cc*p*d-cc*q*d+2*cc+2*p*q*d**2-p*d-2*q*d+1
    ))
    kernel = trunc(
        root**sp.Rational(-3, 2)*companion("A")*exp_correction
    )
    hregular = trunc(
        root**sp.Rational(-5, 2)*companion("B")*exp_correction
    )
    integrands = {
        "KD": trunc(kernel*d_weight),
        "KF": trunc(kernel*f_over),
        "HDD": trunc(hregular*d_weight**2),
        "HDF": trunc(hregular*d_weight*f_over),
    }

    def gaussian_expectation(poly):
        total = sp.S.Zero
        for (i, j), coefficient in sp.Poly(
            sp.expand(poly), sigma, tau
        ).terms():
            if i % 2 or j % 2:
                continue
            mi = sp.factorial2(i-1)/c**(i//2) if i else 1
            mj = sp.factorial2(j-1)/c**(j//2) if j else 1
            total += coefficient*mi*mj
        return sp.cancel(total)

    moments = {
        name: [
            gaussian_expectation(value.coeff(d, order))
            for order in range(RETAINED)
        ]
        for name, value in integrands.items()
    }
    bilinear = [
        sp.cancel(sum(
            moments["KD"][j]*moments["HDF"][n-j]
            - moments["KF"][j]*moments["HDD"][n-j]
            for j in range(n+1)
        ))
        for n in range(RETAINED)
    ]
    if bilinear[0] != 0:
        raise AssertionError(f"B(0) is not zero: {bilinear[0]}")

    bilinear_series = sum(
        d**n*bilinear[n] for n in range(1, RETAINED)
    )
    kd_series = sum(
        d**n*moments["KD"][n] for n in range(RETAINED)
    )
    y = sp.series(
        bilinear_series/(2*c*d*kd_series**2),
        d,
        0,
        8,
    ).removeO().expand()
    return [sp.cancel(y.coeff(d, order)) for order in range(8)]


def verify() -> list[sp.Expr]:
    x = sp.Rational(29, 40)
    lower = cosine_partial_sum(x, 19)
    upper = cosine_partial_sum(x, 18)
    if not lower < CSTAR < upper:
        raise AssertionError("fixed stress rational is outside S19/S18")

    values = derive_at_fixed_c()
    c_symbol = sp.Symbol("c")
    targets = [
        sp.cancel(value.subs(c_symbol, CSTAR))
        for value in frozen_targets(c_symbol)
    ]
    if len(values) != 8 or len(targets) != 8:
        raise AssertionError((len(values), len(targets)))
    for order, (value, target) in enumerate(zip(values, targets)):
        if value.has(sp.Float):
            raise AssertionError(f"Float contamination at Y{order}")
        difference = sp.cancel(value-target)
        if difference != 0:
            raise AssertionError(
                f"fixed-stress expression mismatch Y{order}: {difference}"
            )
    return values


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest().upper()


def main() -> int:
    path = Path(__file__).resolve()
    root = path.parents[1]
    target_module = root/"scripts"/"surface_remainder_delta0_exact_targets.py"
    prereg = (
        root/"docs"/
        "SURFACE-R7-R8-FIXED-STRESS-EXPRESSION-CHECK-PREREG-20260728.md"
    )
    head = subprocess.check_output(
        ["git", "-c", "safe.directory=*", "rev-parse", "HEAD"],
        cwd=root,
        text=True,
    ).strip()
    print("R7/R8 FIXED-STRESS EXPRESSION CHECK")
    print("git_head", head)
    print("python", platform.python_version())
    print("sympy", sp.__version__)
    print("c_star", CSTAR)
    print("script_sha256", digest(path))
    print("target_module_sha256", digest(target_module))
    print("prereg_sha256", digest(prereg))
    values = verify()
    for order, value in enumerate(values):
        print(f"Y{order}_MATCH numerator_bits={int(value.p).bit_length()} "
              f"denominator_bits={int(value.q).bit_length()}")
    print("R7/R8 FIXED-STRESS EXPRESSION CHECK PASS")
    print(
        "SCOPE exact pointwise corroboration near t=2.9 only; "
        "complex disk, companions, K2, K4, and theorem remain open"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
