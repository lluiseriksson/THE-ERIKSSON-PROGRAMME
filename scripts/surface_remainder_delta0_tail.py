"""Analytic outer-tail bounds for the regular delta=0 endpoint lane.

The bounds cover the part of the moving scaled physical square outside
[0,12]^2 for every 0<=delta<=1/100.  They are absolute moment bounds; the
core and fixed completion still have to be assembled separately.
"""

from dataclasses import dataclass

from flint import arb, ctx

from surface_bessel_integral_remainder import relative_enclosure_invz
from surface_remainder_arb_jet2 import hull


@dataclass(frozen=True)
class TailBounds:
    kd: arb
    kn: arb
    hdd_over_delta2: arb
    gn: arb


def tail_bounds() -> TailBounds:
    cmin = arb(2).sqrt()/2
    u = arb("0.6").sin()**2
    sinc = arb("0.6").sin()/arb("0.6")
    k = sinc**2/4
    rate = 2*cmin*(1-u)*k
    root_min = (1-2*u).sqrt()
    invz_max = arb("0.01")/(4*cmin*root_min)
    invz = hull(arb(0), invz_max)
    arel = arb(relative_enclosure_invz(invz, "A", 4, 20).abs_upper())
    brel = arb(relative_enclosure_invz(invz, "B", 4, 20).abs_upper())
    common = 1/(2*arb.pi()).sqrt()
    kmax = (2*common/(4*cmin)**(arb(3)/2)
            *root_min**(-arb(3)/2)*arel)
    hmax = (common/(4*cmin)**(arb(5)/2)
            *root_min**(-arb(5)/2)*brel)

    radius = arb(12)
    exponential = (-rate*radius**2).exp()
    t0 = exponential/(2*rate*radius)
    t2 = radius*exponential/(2*rate)+t0/(2*rate)
    g0 = arb.pi().sqrt()/(2*rate.sqrt())
    g2 = arb.pi().sqrt()/(4*rate**(arb(3)/2))
    union0 = 2*t0*g0
    # sigma^2 is asymmetric: one strip carries its tail moment, the other
    # carries the full sigma moment times the tau tail.
    union_sigma2 = t2*g0+g2*t0
    bracket = 3+6*u+2*u**2
    quadrants = arb(4)
    kd = quadrants*2*kmax*union0
    kn = quadrants*kmax*(bracket*union_sigma2+3*union0)
    hdd = quadrants*4*hmax*union0
    gn = quadrants*2*hmax*(bracket*union_sigma2+3*union0)
    return TailBounds(kd, kn, hdd, gn)


def check() -> None:
    ctx.prec = 180
    bounds = tail_bounds()
    assert all(value.is_finite() and value > 0
               for value in bounds.__dict__.values())
    print({name: value.str(12) for name, value in bounds.__dict__.items()})
    print("DELTA0 OUTER TAIL BOUNDED ANALYTICALLY")


if __name__ == "__main__":
    check()
