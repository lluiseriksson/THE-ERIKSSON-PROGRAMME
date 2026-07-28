"""Certify X_main >= -1/20 by a true-companion centered covariance."""

from __future__ import annotations

from fractions import Fraction
from math import factorial
import hashlib
from pathlib import Path
import platform
import subprocess

import flint
from flint import arb, ctx

from surface_bessel_integral_remainder import relative_enclosure_invz
from surface_remainder_arb_jet2 import hull
from surface_remainder_delta0_moving_tail import (
    gaussian_quadrant_tail_even,
)


ROOT = Path(__file__).resolve().parents[1]
DELTA_MAX = Fraction(9, 1000)
T_MIN = Fraction(21, 10)
PI_UP = Fraction(31_415_927, 10_000_000)
DELTA_BOXES = 18
T_BOXES = 32
GRID_LADDER = (24, 48)
SIDE = Fraction(12)
PHYSICAL_SIDE = Fraction(6, 5)
SINC_TERMS = 32
ARB_BITS = 180
TARGET = Fraction(-1, 20)
DEPENDENCIES = (
    "scripts/certify_surface_k2_weak_main_covariance.py",
    "scripts/surface_bessel_integral_remainder.py",
    "scripts/surface_remainder_delta0_moving_tail.py",
    "docs/SURFACE-K2-WEAK-MAIN-COVARIANCE-PREREG-20260728.md",
    "docs/SURFACE-HIGH-BETA-WEAK-MAIN-RELAY-PREREG-20260728.md",
)


def aq(value: Fraction | int) -> arb:
    value = Fraction(value)
    return arb(value.numerator)/value.denominator


def pm1() -> arb:
    return arb("0 +/- 1")


def positive_interval(upper: arb) -> arb:
    upper = arb(upper.upper())
    return upper/2+upper/2*pm1()


def symmetric_interval(radius: arb) -> arb:
    return arb(radius.upper())*pm1()


def sha256(relative: str) -> str:
    return hashlib.sha256((ROOT/relative).read_bytes()).hexdigest().upper()


def current_head() -> str:
    return subprocess.check_output(
        ["git", "-c", "safe.directory=*", "rev-parse", "HEAD"],
        cwd=ROOT,
        text=True,
    ).strip()


def sinc_square_over_delta(delta: arb, coordinate: arb) -> arb:
    """Enclose sin(sqrt(delta)*x/2)^2/delta, including delta=0."""

    x = coordinate**2/4
    total = arb(0)
    for n in range(SINC_TERMS):
        coefficient = aq(Fraction(
            (-1)**n*2**(2*n+1),
            factorial(2*n+2),
        ))
        total += coefficient*x*(delta*x)**n

    delta_abs = arb(delta.abs_upper())
    x_abs = arb(x.abs_upper())

    def absolute_term(n: int) -> arb:
        return (
            aq(Fraction(2**(2*n+1), factorial(2*n+2)))
            * x_abs
            * (delta_abs*x_abs)**n
        )

    tail = sum(
        (absolute_term(n) for n in range(SINC_TERMS, 200)),
        arb(0),
    )
    term_200 = absolute_term(200)
    term_201 = absolute_term(201)
    ratio = term_201/term_200 if term_200 > 0 else arb(0)
    if not arb(ratio.upper()) < arb(1)/2:
        raise AssertionError(f"sinc tail is not contractive: {ratio}")
    tail += term_200/(1-ratio)
    return total+arb(tail.upper())*pm1()


def centered_integrands(
    delta: arb,
    t: arb,
    sigma: arb,
    tau: arb,
) -> dict[str, arb]:
    p = sinc_square_over_delta(delta, sigma)
    q = sinc_square_over_delta(delta, tau)
    c = (t/4).cos()
    c2 = c**2
    cc = 2*c2-1
    w = p+q-delta*p*q/c2
    root2 = 1-delta*w
    if not arb(root2.lower()) > 0:
        raise AssertionError(f"root square is unresolved: {root2}")
    root = root2.sqrt()
    phase = -4*c*w/(1+root)
    h = delta/(4*c*root)
    a_relative = relative_enclosure_invz(h, "A", order=4, z0=20)
    b_relative = relative_enclosure_invz(h, "B", order=4, z0=20)
    if not arb(a_relative.lower()) > 0:
        raise AssertionError(f"A companion is unresolved: {a_relative}")

    d_weight = 2*(1-delta*(p+q))
    if not arb(d_weight.lower()) > 0:
        raise AssertionError(f"D is unresolved: {d_weight}")
    bracket = (
        -2*cc*delta*p
        - cc*delta*q
        + 2*cc+1
        + 2*delta**2*p*q
        - delta*p
        - 2*delta*q
    )
    f_weight = -4*p*bracket
    common = 1/(2*arb.pi()).sqrt()
    exponential = phase.exp()
    kernel = (
        2*common/(4*c)**(arb(3)/2)
        * root**(-arb(3)/2)
        * a_relative
    )
    h_prefactor = (
        common/(4*c)**(arb(5)/2)
        * root**(-arb(5)/2)
    )
    centered = b_relative*d_weight-2*root*a_relative
    return {
        "kd": kernel*d_weight*exponential,
        "kf": kernel*f_weight*exponential,
        "gdd": h_prefactor*d_weight*centered*exponential,
        "gdf": h_prefactor*f_weight*centered*exponential,
    }


def core_moments(delta: arb, t: arb, grid: int) -> dict[str, arb]:
    totals = {name: arb(0) for name in ("kd", "kf", "gdd", "gdf")}
    width = aq(SIDE)/grid
    area = 4*width**2
    for i in range(grid):
        sigma = hull(width*i, width*(i+1))
        for j in range(grid):
            tau = hull(width*j, width*(j+1))
            values = centered_integrands(delta, t, sigma, tau)
            for name, value in values.items():
                totals[name] += area*value
    return totals


def uniform_tail_charges() -> dict[str, arb]:
    cmin = arb(2).sqrt()/2
    physical_half = aq(Fraction(3, 5))
    u = physical_half.sin()**2
    if not arb(u.upper()) < arb(1)/3:
        raise AssertionError(f"u<1/3 was not certified: {u}")
    # With |cc|<=1 and P,Q<=u, the absolute bracket multiplying -4p is
    # at most 3+6u+2u^2<6.  Since p<=sigma^2/4, |F|<=6r^2.
    assert (
        Fraction(3)+6*Fraction(1, 3)+2*Fraction(1, 9)
        < Fraction(6)
    )
    root_min = (1-2*u).sqrt()
    sinc = physical_half.sin()/physical_half
    rate = cmin/2*(1-u)*sinc**2
    if not arb(rate.lower()) > 0:
        raise AssertionError(f"tail rate is unresolved: {rate}")

    hmax = aq(DELTA_MAX)/(4*cmin*root_min)
    hbox = positive_interval(hmax)
    a_relative = relative_enclosure_invz(
        hbox, "A", order=4, z0=20
    )
    b_relative = relative_enclosure_invz(
        hbox, "B", order=4, z0=20
    )
    if not arb(a_relative.lower()) > 0:
        raise AssertionError("tail A companion has no positive floor")
    ratio_abs = arb((b_relative/a_relative).abs_upper())
    common = 1/(2*arb.pi()).sqrt()
    kernel_constant = (
        2*common/(4*cmin)**(arb(3)/2)
        * root_min**(-arb(3)/2)
        * arb(a_relative.abs_upper())
    )
    g_abs = (
        ratio_abs/(4*cmin*root_min)
        + 1/(4*cmin)
    )

    radius = aq(SIDE)
    quadrant_0 = gaussian_quadrant_tail_even(rate, radius, 0)
    quadrant_2 = gaussian_quadrant_tail_even(rate, radius, 2)
    mass = 4*2*kernel_constant*quadrant_0
    fmoment = 4*6*kernel_constant*quadrant_2
    return {
        "rate": rate,
        "kernel_constant": kernel_constant,
        "g_abs": g_abs,
        "kd": arb(mass.upper()),
        "kf": arb(fmoment.upper()),
        "gdd": arb((g_abs*mass).upper()),
        "gdf": arb((g_abs*fmoment).upper()),
    }


def judge(
    delta: arb,
    t: arb,
    grid: int,
    tail: dict[str, arb],
) -> tuple[arb, arb]:
    core = core_moments(delta, t, grid)
    if not arb(core["kd"].lower()) > 0:
        raise AssertionError(f"core KD has no positive floor: {core['kd']}")
    moments = {
        "kd": core["kd"]+positive_interval(tail["kd"]),
        "kf": core["kf"]+symmetric_interval(tail["kf"]),
        "gdd": core["gdd"]+symmetric_interval(tail["gdd"]),
        "gdf": core["gdf"]+symmetric_interval(tail["gdf"]),
    }
    xmain = 4*(
        moments["kd"]*moments["gdf"]
        - moments["kf"]*moments["gdd"]
    )/moments["kd"]**2
    return core["kd"], xmain


def certify() -> dict[str, object]:
    ctx.prec = ARB_BITS
    assert aq(SIDE)*aq(DELTA_MAX).sqrt() < aq(PHYSICAL_SIDE)
    assert (aq(T_MIN)/4).sin() < aq(Fraction(101, 200))
    assert aq(PI_UP) > arb.pi()
    tail = uniform_tail_charges()
    target = aq(TARGET)
    worst_lower = arb(1)
    worst_label = ""
    grid_counts = {grid: 0 for grid in GRID_LADDER}
    rows = []
    delta_width = DELTA_MAX/DELTA_BOXES
    t_width = (PI_UP-T_MIN)/T_BOXES
    for di in range(DELTA_BOXES):
        dlo = delta_width*di
        dhi = delta_width*(di+1)
        delta = hull(aq(dlo), aq(dhi))
        for ti in range(T_BOXES):
            tlo = T_MIN+t_width*ti
            thi = T_MIN+t_width*(ti+1)
            t = hull(aq(tlo), aq(thi))
            accepted = None
            for grid in GRID_LADDER:
                kd, xmain = judge(delta, t, grid, tail)
                if arb(xmain.lower()) > target:
                    accepted = (grid, kd, xmain)
                    break
            if accepted is None:
                raise AssertionError(
                    f"weak-main target failed d={di} t={ti}: {xmain}"
                )
            grid, kd, xmain = accepted
            grid_counts[grid] += 1
            lower = arb(xmain.lower())
            if lower < worst_lower:
                worst_lower = lower
                worst_label = f"d{di}:t{ti}:g{grid}"
            rows.append((di, ti, dlo, dhi, tlo, thi, grid, kd, xmain))
    return {
        "tail": tail,
        "rows": rows,
        "grid_counts": grid_counts,
        "worst_lower": worst_lower,
        "worst_label": worst_label,
    }


def main() -> int:
    print("PROVENANCE git_head", current_head())
    print("PROVENANCE python", platform.python_version())
    print("PROVENANCE python_flint", flint.__version__)
    print("PROVENANCE arb_bits", ARB_BITS)
    for relative in DEPENDENCIES:
        print("DEPENDENCY", relative, sha256(relative))
    result = certify()
    tail = result["tail"]
    print("WEAK MAIN TRUE-COMPANION COVARIANCE PASS")
    print(
        "CONFIG delta=0:9/1000:18 t=21/10:31415927/10000000:32 "
        "side=12 grids=24,48 companion_order=4 z0=20"
    )
    for name in ("rate", "kernel_constant", "g_abs", "kd", "kf", "gdd", "gdf"):
        print("TAIL", name, tail[name].str(50))
    for row in result["rows"]:
        di, ti, dlo, dhi, tlo, thi, grid, kd, xmain = row
        print(
            "ROW",
            di,
            ti,
            f"{dlo}:{dhi}",
            f"{tlo}:{thi}",
            "grid",
            grid,
            "KD",
            kd.str(18),
            "XMAIN",
            xmain.str(18),
        )
    print("GRID_COUNTS", result["grid_counts"])
    print(
        "WORST_LOWER",
        result["worst_lower"].str(50),
        "at",
        result["worst_label"],
        "> -1/20",
    )
    print(
        "SCOPE weak X_main premise only; "
        "terminal union and manuscript remain open"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
