"""Symbolic audit of the exact five-family right-edge scaling."""

import sympy as sp


def verify():
    beta, lam, rho = sp.symbols("beta lambda rho", positive=True)
    delta = 1/beta
    y = lam**2/(4*beta**2)
    j, jy, s, sy = sp.symbols("j jy s sy")
    U0, U1, U2, B0, B1 = sp.symbols("U0 U1 U2 B0 B1")

    U = U0/(rho*sp.sqrt(beta))
    Uy = U1*beta**sp.Rational(3, 2)/rho
    Uyy = U2*beta**sp.Rational(7, 2)/rho
    b = B0*sp.sqrt(beta)/rho
    by = B1*beta**sp.Rational(5, 2)/rho
    a = j*U+2*s*Uy
    ay = jy*U+(j+2*sy)*Uy+2*s*Uyy
    A0 = sp.simplify(rho*beta**sp.Rational(-3, 2)*a)
    A1 = sp.simplify(rho*beta**sp.Rational(-7, 2)*ay)
    assert sp.simplify(A0-(j*delta**2*U0+2*s*U1)) == 0
    assert sp.simplify(
        A1-(jy*delta**4*U0+(j+2*sy)*delta**2*U1+2*s*U2)
    ) == 0

    P = a*b+y*(ay*b-a*by)
    P0 = sp.simplify(rho**2*beta**-2*P)
    advertised = A0*B0+lam**2*(A1*B0-A0*B1)/4
    assert sp.simplify(P0-advertised) == 0
    H = sp.simplify(delta*P/(4*b**2))
    assert sp.simplify(H-P0/(4*B0**2)) == 0

    u, shift = sp.symbols("u shift", real=True)
    plus = sp.expand_trig(sp.sin(u)+sp.cos(u+shift))
    minus = sp.expand_trig(sp.sin(u)-sp.cos(u+shift))
    plus_norm2 = sp.expand((1-sp.sin(shift))**2+sp.cos(shift)**2)
    minus_norm2 = sp.expand((1+sp.sin(shift))**2+sp.cos(shift)**2)
    assert sp.trigsimp(plus_norm2-(2-2*sp.sin(shift))) == 0
    assert sp.trigsimp(minus_norm2-(2+2*sp.sin(shift))) == 0
    assert sp.trigsimp(
        plus-((1-sp.sin(shift))*sp.sin(u)+sp.cos(shift)*sp.cos(u))
    ) == 0
    assert sp.trigsimp(
        minus-((1+sp.sin(shift))*sp.sin(u)-sp.cos(shift)*sp.cos(u))
    ) == 0
    print(
        "RIGHT-EDGE FIVE-FAMILY SCALING PASS: "
        "H=P0/(4 B0^2), exact beta powers and two phase amplitudes"
    )


if __name__ == "__main__":
    verify()
