"""Independent Arb oracle for the exact Poisson Bessel representation.

Composite interval sums enclose the integral directly on every theta cell;
the comparison value uses Arb's Bessel implementation.  This audits the
identity used by the K4 regular-ball design.  It is not a coefficient, tail,
or weighted-union certificate.
"""

from flint import arb, ctx

from surface_remainder_arb_jet2 import hull


def poisson_integral(z, nu, grid):
    z = arb(z)
    width = arb.pi()/grid
    total = arb(0)
    for index in range(grid):
        theta = hull(index*width, (index+1)*width)
        integrand = (-z*(1-theta.cos())).exp()*(nu*theta).cos()
        total += integrand*width
    return total/arb.pi()


def direct(z, nu):
    z = arb(z)
    return (-z).exp()*z.bessel_i(nu)


def verify_case(z, nu, grid):
    integral = poisson_integral(z, nu, grid)
    target = direct(z, nu)
    assert integral.overlaps(target)
    return integral, target


def verify_all():
    ctx.prec = 140
    rows = []
    for z, grid in ((30, 4096), (50, 8192), (800, 32768)):
        for nu in (0, 1):
            integral, target = verify_case(z, nu, grid)
            rows.append((z, nu, grid, integral, target))
    return rows


if __name__ == "__main__":
    for z, nu, grid, integral, target in verify_all():
        print("K4 POISSON ORACLE PASS", "z", z, "nu", nu, "grid", grid,
              "integral", integral.str(30), "direct", target.str(30))
    print("K4 POISSON REPRESENTATION AUDITED; TAIL CERTIFICATE STILL OPEN")
