"""Shift-centered complex-circle covariance for the nominal fixed square."""

from __future__ import annotations

from flint import acb, arb, ctx

import probe_surface_k2_fixed_square_complex_supremum as base


LADDER = ((24, 32), (48, 64), (96, 128))


def raw_point(delta: acb, sigma: arb, alpha: arb):
    c = (base.T/4).cos()
    p = base.p_over_delta(delta, sigma)
    q = base.p_over_delta(delta, alpha)
    w = p+q-delta*p*q/c**2
    root = (1-delta*w).sqrt()
    phase = -4*c*w/(1+root)
    h = delta/(4*c*root)
    acomp = base.relative_polynomial(h, "A")
    bcomp = base.relative_polynomial(h, "B")
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
    return weight, a, g


def midpoint(value: acb) -> acb:
    return acb(value.real.mid(), value.imag.mid())


def assemble_centered(cells):
    mass = sum((area*weight for area, weight, _, _ in cells), acb(0))
    wa = sum((area*weight*a for area, weight, a, _ in cells), acb(0))
    wg = sum((area*weight*g for area, weight, _, g in cells), acb(0))
    a0, g0 = midpoint(wa/mass), midpoint(wg/mass)
    sda = sum(
        (area*weight*(a-a0) for area, weight, a, _ in cells),
        acb(0),
    )
    sdg = sum(
        (area*weight*(g-g0) for area, weight, _, g in cells),
        acb(0),
    )
    sdag = sum(
        (
            area*weight*(a-a0)*(g-g0)
            for area, weight, a, g in cells
        ),
        acb(0),
    )
    y = 4*(sdag/mass-(sda/mass)*(sdg/mass))
    return mass, a0, g0, y


def integrate_arc(grid: int, theta_index: int, theta_count: int):
    delta = base.theta_arc(theta_index, theta_count)
    width = base.SIDE/grid
    cells = []
    for i in range(grid):
        for j in range(grid):
            sigma = base.hull(width*i, width*(i+1))
            alpha = base.hull(width*j, width*(j+1))
            weight, a, g = raw_point(delta, sigma, alpha)
            cells.append((4*width**2, weight, a, g))
    mass, a0, g0, y = assemble_centered(cells)
    return delta, mass, a0, g0, y


def run(grid: int, theta_count: int):
    worst = arb(0)
    mass_floor = None
    for index in range(theta_count):
        delta, mass, a0, g0, y = integrate_arc(
            grid, index, theta_count
        )
        lower = arb(abs(mass).lower())
        mass_floor = lower if mass_floor is None else min(mass_floor, lower)
        y_upper = arb(abs(y).upper())
        worst = max(worst, y_upper)
        print(
            "ARC",
            index,
            "DELTA",
            delta,
            "MASS_ABS_LOWER",
            lower,
            "A0",
            a0,
            "G0",
            g0,
            "Y_ABS_UPPER",
            y_upper,
            flush=True,
        )
    return mass_floor, worst


def main() -> int:
    ctx.prec = 140
    available, multiplier, required_m = base.cauchy_budget()
    print("K2 FIXED-SQUARE CENTERED COMPLEX SUPREMUM DESIGN")
    print("rho", base.RHO, "delta_max", base.DELTA_MAX)
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
        "K2 FIXED-SQUARE CENTERED COMPLEX SUPREMUM DESIGN "
        + ("PASS" if passed else "FAIL")
        + "; EXTERIOR AND TRUE COMPANION OPEN",
        flush=True,
    )
    return 0 if passed else 1


if __name__ == "__main__":
    raise SystemExit(main())
