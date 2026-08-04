"""Exact/Arb audit of the angular partition and tail phase constants."""

from fractions import Fraction

import sympy as sp
from flint import arb, ctx


def verify():
    ctx.prec = 160
    u, eta = sp.symbols("u eta", real=True)
    plus_amp = 2*sp.sin(sp.pi/4-eta/2)
    minus_amp = 2*sp.cos(sp.pi/4-eta/2)
    assert sp.trigsimp(
        sp.sin(u)+sp.cos(u+eta)
        -plus_amp*sp.cos(u-(sp.pi/4-eta/2))) == 0
    assert sp.trigsimp(
        sp.sin(u)-sp.cos(u+eta)
        -minus_amp*sp.cos(u-(3*sp.pi/4-eta/2))) == 0
    a = sp.symbols("a", real=True)
    assert sp.trigsimp(
        sp.cos(a)-sp.sin(a+eta)
        -plus_amp*sp.cos(a-(-sp.pi/4-eta/2))) == 0
    assert sp.trigsimp(
        sp.cos(a)+sp.sin(a+eta)
        -minus_amp*sp.cos(a-(sp.pi/4-eta/2))) == 0

    pi = arb.pi()
    shift = arb(3)/500
    assert 2*(pi/8).sin() > arb(3)/4
    assert 2*(pi/8-shift).sin() > arb(3)/4
    assert 4/arb(125).sqrt() < pi/8-shift/2
    amplitude = (2-2*shift.sin()).sqrt()
    sinc_floor = 1-arb(1)/150
    # The largest chart displacement is strictly below pi/8+shift/2.
    # Link the declared rational floor to the actual sinc at that edge;
    # monotonicity of sinc on this positive interval then covers every chart
    # point.  This assert prevents the Gaussian rate from becoming a free
    # numerical constant detached from the frozen chart.
    chart_edge = pi/8+shift/2
    sinc_argument = chart_edge/2
    assert sinc_argument.sin()/sinc_argument > sinc_floor
    assert amplitude*sinc_floor**2 > arb(4)/3
    endpoint = (pi/8).sin()+(pi/8).cos()
    assert endpoint < arb(131)/100
    assert arb(2).sqrt() > arb(707)/500
    shifted_exact = Fraction(131, 100)+Fraction(3, 500)
    assert shifted_exact == Fraction(329, 250)
    doubled_exact = 2*(Fraction(707, 500)-shifted_exact)
    assert doubled_exact == Fraction(49, 250)
    doubled_gap = arb(doubled_exact.numerator)/doubled_exact.denominator
    assert doubled_gap > arb(3)/(2*125)
    print(
        "RIGHT-EDGE FIVE-FAMILY TAIL GEOMETRY PASS: moving saddles, "
        "v>=3/4, Gaussian rate 4/3, exterior doubled gap 49/250"
    )


if __name__ == "__main__":
    verify()
