"""Exact interval audit of the z>=8 central-chart floor for beta>=20."""

from fractions import Fraction

from flint import arb, ctx


def verify():
    ctx.prec = 160
    delta_max = arb(1)/20
    side = arb(5)/2
    eta_max = delta_max*arb(3)/4
    displacement = delta_max.sqrt()*side
    angle_floor = arb.pi()/4-eta_max/2-displacement
    value_floor = 2*angle_floor.sin()
    assert angle_floor > 0
    assert value_floor > arb(25)/62
    assert Fraction(1, 20)/Fraction(25, 62) == Fraction(31, 250)
    assert Fraction(31, 250) < Fraction(1, 8)
    return angle_floor, value_floor


def main():
    angle, value = verify()
    print("BETA20 CENTRAL GEOMETRY PASS angle_floor", angle,
          "bessel_value_floor", value, "z_floor > 8")


if __name__ == "__main__":
    main()
