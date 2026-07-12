"""Ball-series design probe for the head-subtracted delta=0 lane.

This propagates formal delta derivatives of the regular nominal carrier.
It deliberately omits the Bessel companion remainder and the analytic
outer derivative tail, so its output is design evidence only.
"""

from fractions import Fraction
from math import factorial

from flint import arb, arb_series, ctx

from surface_bessel_integral_remainder import relative_coefficients
from surface_remainder_arb_jet2 import hull


PREC = 6


def aq(value: Fraction) -> arb:
    return arb(value.numerator)/arb(value.denominator)


def sinc2_derivatives(y: arb, max_order: int, terms: int = 28) -> list[arb]:
    """Derivatives of sinc(sqrt(y))^2 with explicit series tails."""
    ymax = arb(y.abs_upper())
    out = [arb(0) for _ in range(max_order+1)]
    for n in range(terms):
        coefficient = arb((-1)**n*2**(2*n+1))/factorial(2*n+2)
        for order in range(min(n, max_order)+1):
            falling = factorial(n)//factorial(n-order)
            out[order] += coefficient*falling*y**(n-order)
    for order in range(max_order+1):
        n = max(terms, order)
        falling = factorial(n)//factorial(n-order)
        first = (arb(2**(2*n+1))/factorial(2*n+2)
                 *falling*ymax**(n-order))
        ratio = (4*ymax*arb(n+1)/arb(n+1-order)
                 /arb((2*n+4)*(2*n+3)))
        if not ratio < arb(1)/2:
            raise ValueError("sinc derivative tail is not contractive")
        out[order] += first/(1-ratio)*arb("0 +/- 1")
    return out


def sinc2_affine_delta(base: arb, scale: arb, prec: int = PREC) -> arb_series:
    derivatives = sinc2_derivatives(scale*base, prec-1)
    return arb_series([
        derivatives[k]*scale**k/factorial(k) for k in range(prec)
    ], prec)


def relative_polynomial_series(h: arb_series, family: str) -> arb_series:
    out = arb_series([arb(0)], h.prec)
    for coefficient in reversed(relative_coefficients(family, 4)):
        out = out*h+aq(coefficient)
    return out


def nominal_moment_series(base: arb, t: arb, sigma: arb,
                          tau: arb, prec: int = PREC):
    """Nominal A/B-polynomial moment series around a delta base ball."""
    d = arb_series([base, arb(1)], prec)
    sigma2, tau2 = sigma**2, tau**2
    p_over = sigma2/4*sinc2_affine_delta(base, sigma2/4, prec)
    q_over = tau2/4*sinc2_affine_delta(base, tau2/4, prec)
    c = (t/4).cos(); c2 = c**2; cc = 2*c2-1
    w_over = p_over+q_over-d*p_over*q_over/c2
    root = (1-d*w_over).sqrt()
    phase = -4*c*w_over/(1+root)
    h = d/(4*c*root)
    d_weight = 2*(1-d*(p_over+q_over))
    bracket = (-2*cc*d*p_over-cc*d*q_over+2*cc+1
               +2*d**2*p_over*q_over-d*p_over-2*d*q_over)
    f_over = -4*p_over*bracket
    common = 1/(2*arb.pi()).sqrt()
    kernel = (2*common/(4*c)**(arb(3)/2)*root**(-arb(3)/2)
              *relative_polynomial_series(h, "A"))
    hregular = (common/(4*c)**(arb(5)/2)*root**(-arb(5)/2)
                *relative_polynomial_series(h, "B"))
    exponential = phase.exp()
    return {
        "kd": kernel*d_weight*exponential,
        "kf": kernel*f_over*exponential,
        "hdd": hregular*d_weight**2*exponential,
        "hdf": hregular*d_weight*f_over*exponential,
    }


def integrate_coefficients(t: arb, grid: int = 24, side: int = 12,
                           prec: int = PREC, base: arb = arb(0)):
    totals = {name: [arb(0) for _ in range(prec)]
              for name in ("kd", "kf", "hdd", "hdf")}
    width = arb(side)/grid
    for i in range(grid):
        for j in range(grid):
            sigma = hull(width*i, width*(i+1))
            tau = hull(width*j, width*(j+1))
            values = nominal_moment_series(base, t, sigma, tau, prec)
            area = 4*width**2
            for name, series in values.items():
                coefficients = series.coeffs()
                for order, value in enumerate(coefficients):
                    totals[name][order] += area*value
    return totals


def assemble_y_derivatives(series: dict[str, arb_series], t: arb):
    """Assemble normalized Y derivative coefficients from moment series."""
    bilinear = series["kd"]*series["hdf"]-series["kf"]*series["hdd"]
    coefficients = bilinear.coeffs()+[arb(0)]*PREC
    quotient = arb_series([coefficients[k+1] for k in range(PREC-2)],
                          PREC-2)
    c = (t/4).cos()
    return quotient/(2*c*series["kd"]**2)


def endpoint_series_data(base: arb, t: arb, grid: int = 96,
                         side: int = 12):
    """Enclose normalized derivatives of nominal Y on a base ball.

    If B=KD*HDF-KF*HDD, exact full-plane cancellation gives B(0)=0.
    For Q(delta)=B(delta)/delta, the integral identity

        Q^(k)(delta)/k! = (k+1) int_0^1 s^k
                           B^(k+1)(s delta)/(k+1)! ds

    puts every normalized Q derivative inside the next normalized B
    derivative on a base ball containing zero.  This avoids interval
    division by delta.  The routine remains design-only until the omitted
    Bessel and outer derivative tails are added.
    """
    if not base.contains(arb(0)):
        raise ValueError("the B/delta integral identity expects a zero lane")
    moments = integrate_coefficients(t, grid, side, PREC, base=base)
    series = {name: arb_series(values, PREC)
              for name, values in moments.items()}
    return series, assemble_y_derivatives(series, t)


def normalized_y_derivative_enclosure(base: arb, t: arb, grid: int = 96,
                                      side: int = 12) -> arb_series:
    return endpoint_series_data(base, t, grid, side)[1]


def probe() -> None:
    ctx.prec = 140
    t = arb("2.9")
    for grid in (12, 24, 48):
        totals = integrate_coefficients(t, grid)
        print("grid", grid)
        for name, coefficients in totals.items():
            print(name, [value.str(8) for value in coefficients[:5]])
    lane = hull(arb(0), arb("0.001"))
    derivatives = normalized_y_derivative_enclosure(lane, t, 96)
    print("uniform [0,0.001] nominal Y derivatives",
          [value.str(10) for value in derivatives.coeffs()])
    print("DELTA0 SERIES DESIGN ONLY: BESSEL AND OUTER DERIVATIVE TAILS OPEN")


if __name__ == "__main__":
    probe()
