"""Symbolic audit of the cancellation-free right-edge reduction."""

import sympy as sp


def verify():
    x, delta = sp.symbols("x delta", positive=True)
    y = sp.symbols("y", nonnegative=True)
    U = sp.Function("U")
    V = sp.Function("V")

    # Work first with y=x^2, then compare with the advertised functions.
    ux = U(x**2)
    vx = V(x**2)
    shifted_s = x*ux
    shifted_r = vx
    A = sp.sin(x)*sp.diff(shifted_s, x)-sp.cos(x)*shifted_s
    B = sp.diff(shifted_r, x)/2  # B(2x)=R'(2x)=T'(x)/2
    sinc = sp.sin(x)/x
    j = (sp.sin(x)-x*sp.cos(x))/x**3
    Uy = sp.Subs(sp.Derivative(U(y), y), y, x**2)
    a = j*ux+2*sinc*Uy
    b = sp.Subs(sp.Derivative(V(y), y), y, x**2)
    assert sp.simplify(A-x**3*a) == 0
    assert sp.simplify(B-x*b) == 0

    E = sp.cancel(A/(2*B))
    assert sp.simplify(E-x**2*a/(2*b)) == 0
    lam = 2*x/delta
    H = sp.cancel(sp.diff(E, x)/(2*lam))
    ay = sp.diff(a, x)/(2*x)
    by = sp.diff(b, x)/(2*x)
    P = a*b+x**2*(ay*b-a*by)
    assert sp.simplify(H-delta*P/(4*b**2)) == 0

    # Removable elementary coefficients.
    assert sp.limit(sinc, x, 0) == 1
    assert sp.limit(j, x, 0) == sp.Rational(1, 3)
    print(
        "RIGHT-EDGE DIVIDED-DIFFERENCE PASS: "
        "A=x^3 a, B=x b, H=delta P/(4 b^2); "
        "five-family interval cover remains required"
    )


if __name__ == "__main__":
    verify()
