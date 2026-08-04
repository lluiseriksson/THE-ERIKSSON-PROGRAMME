"""Complex-circle supremum probe for the nominal K2 fixed square.

The removable coordinate ``G`` is evaluated directly on theta arcs.  Spatial
cells are enclosed by interval evaluation, so no complex quadrature heuristic
is used.  This is still design-only: exterior and true-companion errors are
absent.
"""

from __future__ import annotations

from fractions import Fraction
from math import factorial

from flint import acb, arb, ctx

from surface_bessel_integral_remainder import relative_coefficients
from surface_remainder_arb_jet2 import hull
from surface_remainder_delta0_fourth_coefficient import target_y3
from surface_remainder_delta0_fifth_coefficient import target_y4
from surface_remainder_delta0_sixth_coefficient import target_y5
from surface_remainder_s2_direct_judge import closed_forms


RHO = arb(17)/2000
DELTA_MAX = arb(1)/1000
SIDE = arb(12)
T = arb("2.9")
COMPANION_ORDER = 5
P_TERMS = 18
LADDER = ((12, 16), (24, 32), (48, 64))


def complex_error(radius: arb) -> acb:
    return acb(arb(0, radius), arb(0, radius))


def p_over_delta(delta: acb, coordinate: arb) -> acb:
    """Entire series for sin(sqrt(delta)*x/2)^2/delta."""

    x = acb(coordinate)
    x2 = x*x
    unit = delta*x2/4
    total = acb(0)
    power = acb(1)
    for n in range(P_TERMS):
        coefficient = Fraction(
            (-1)**n*2**(2*n+1),
            factorial(2*n+2)*4,
        )
        total += (
            arb(coefficient.numerator)/coefficient.denominator
            * x2*power/4**n
        )
        power *= delta*x2

    xmax = arb(coordinate.upper())
    first_omitted = (
        arb(2**(2*P_TERMS+1))
        / factorial(2*P_TERMS+2)
        * xmax**2/4
        * (RHO*xmax**2/4)**P_TERMS
    )
    ratio = (
        RHO*xmax**2
        / ((2*P_TERMS+4)*(2*P_TERMS+3))
    )
    if not ratio < 1:
        raise ValueError("p-series tail ratio is not contractive")
    return total+complex_error(first_omitted/(1-ratio))


def relative_polynomial(h: acb, family: str) -> acb:
    out = acb(0)
    for coefficient in reversed(
        relative_coefficients(family, COMPANION_ORDER)
    ):
        out = out*h+arb(coefficient.numerator)/coefficient.denominator
    return out


def point(delta: acb, sigma: arb, alpha: arb):
    c = (T/4).cos()
    p = p_over_delta(delta, sigma)
    q = p_over_delta(delta, alpha)
    w = p+q-delta*p*q/c**2
    root = (1-delta*w).sqrt()
    phase = -4*c*w/(1+root)
    h = delta/(4*c*root)
    acomp = relative_polynomial(h, "A")
    bcomp = relative_polynomial(h, "B")
    d = 2*(1-delta*(p+q))
    cc = 2*c**2-1
    bracket = (
        -2*cc*delta*p-cc*delta*q+2*cc+1
        +2*delta**2*p*q-delta*p-2*delta*q
    )
    f = -4*p*bracket
    common = 1/(2*arb.pi()).sqrt()
    root_inv = 1/root
    root_half_inv = 1/root.sqrt()
    kernel = (
        2*common/(4*c)**(arb(3)/2)
        * root_inv*root_half_inv*acomp*phase.exp()
    )
    ratio = 8*c*root*acomp/bcomp
    r = d/ratio
    g = (r-1/(4*c))/delta
    a = f/d
    weight = kernel*d
    return weight, weight*a, weight*g, weight*a*g


def theta_arc(index: int, count: int) -> acb:
    lo = 2*arb.pi()*index/count
    hi = 2*arb.pi()*(index+1)/count
    theta = hull(lo, hi)
    return acb(RHO*theta.cos(), RHO*theta.sin())


def integrate_arc(grid: int, theta_index: int, theta_count: int):
    delta = theta_arc(theta_index, theta_count)
    width = SIDE/grid
    totals = [acb(0) for _ in range(4)]
    for i in range(grid):
        for j in range(grid):
            sigma = hull(width*i, width*(i+1))
            alpha = hull(width*j, width*(j+1))
            values = point(delta, sigma, alpha)
            area = 4*width**2
            for k, value in enumerate(values):
                totals[k] += area*value
    mass, wa, wg, wag = totals
    y = 4*(wag/mass-(wa/mass)*(wg/mass))
    return delta, mass, y


def cauchy_budget():
    leading, r2, r3, theta3 = closed_forms(T)
    c = (T/4).cos()
    r4, r5, r6 = target_y3(c), target_y4(c), target_y5(c)
    retained = r3+r4*DELTA_MAX+r5*DELTA_MAX**2+r6*DELTA_MAX**3
    available = (
        theta3-arb(retained.abs_upper())
    )*DELTA_MAX**2
    q = DELTA_MAX/RHO
    multiplier = q**6/(1-q)
    return available, multiplier, available/multiplier


def run(grid: int, theta_count: int):
    worst = arb(0)
    mass_floor = None
    for index in range(theta_count):
        delta, mass, y = integrate_arc(grid, index, theta_count)
        mass_abs = abs(mass)
        lower = arb(mass_abs.lower())
        mass_floor = lower if mass_floor is None else min(mass_floor, lower)
        y_abs = abs(y)
        worst = max(worst, arb(y_abs.upper()))
        print(
            "ARC",
            index,
            "DELTA",
            delta,
            "MASS_ABS_LOWER",
            lower,
            "Y_ABS_UPPER",
            arb(y_abs.upper()),
            flush=True,
        )
    return mass_floor, worst


def main() -> int:
    ctx.prec = 140
    available, multiplier, required_m = cauchy_budget()
    print("K2 FIXED-SQUARE COMPLEX SUPREMUM DESIGN")
    print("rho", RHO, "delta_max", DELTA_MAX)
    print("available_remainder", available)
    print("cauchy_multiplier", multiplier)
    print("required_M", required_m)
    passed = False
    for grid, theta_count in LADDER:
        try:
            mass_floor, worst = run(grid, theta_count)
        except (ValueError, ZeroDivisionError) as exc:
            print(
                "LEVEL",
                grid,
                theta_count,
                "UNRESOLVED",
                type(exc).__name__,
                str(exc),
                flush=True,
            )
            continue
        passed = (
            arb(mass_floor.lower()) > 0
            and worst.is_finite()
            and arb(worst.upper()) < required_m
        )
        print(
            "LEVEL",
            grid,
            theta_count,
            "MASS_FLOOR",
            mass_floor,
            "M_SUP",
            worst,
            "PASS",
            passed,
            flush=True,
        )
        if passed:
            break
    print(
        "K2 FIXED-SQUARE COMPLEX SUPREMUM DESIGN "
        + ("PASS" if passed else "FAIL")
        + "; EXTERIOR AND TRUE COMPANION OPEN",
        flush=True,
    )
    return 0 if passed else 1


if __name__ == "__main__":
    raise SystemExit(main())
