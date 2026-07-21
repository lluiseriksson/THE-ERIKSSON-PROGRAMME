"""Bivariate parameter jets for the K2 remainder route.

This module is deliberately *design/probe* infrastructure.  A ``BiJet``
stores the Taylor coefficients

    f(d+h, t+k) = c00 + c10*h + c01*k + c20*h^2 + c11*h*k + c02*k^2 + O(3).

The coefficients are Arb balls and the algebra is truncated at total degree
two.  It preserves the mixed delta--t coefficient, which is the datum missing
from the existing univariate ``Jet`` implementations.  No global enclosure
claim is made here: a future certificate must add explicit third-order
remainders and integrate the signed bilinear form before taking spatial
absolute values.
"""

from __future__ import annotations

from dataclasses import dataclass

from flint import arb, ctx

from surface_remainder_arb_jet2 import g_derivatives, h_derivatives, hull


def A(value: object) -> arb:
    return value if isinstance(value, arb) else arb(str(value))


@dataclass(frozen=True)
class BiJet:
    c00: arb
    c10: arb = arb(0)  # delta coefficient
    c01: arb = arb(0)  # t coefficient
    c20: arb = arb(0)
    c11: arb = arb(0)
    c02: arb = arb(0)


def lift(value: object) -> BiJet:
    return value if isinstance(value, BiJet) else BiJet(A(value))


def _coeffs(value: BiJet) -> tuple[arb, ...]:
    return (value.c00, value.c10, value.c01, value.c20, value.c11, value.c02)


def add(a: object, b: object) -> BiJet:
    a, b = lift(a), lift(b)
    return BiJet(*(x + y for x, y in zip(_coeffs(a), _coeffs(b))))


def neg(a: object) -> BiJet:
    a = lift(a)
    return BiJet(*(-x for x in _coeffs(a)))


def sub(a: object, b: object) -> BiJet:
    return add(a, neg(b))


def scale(a: object, value: object) -> BiJet:
    return mul(a, A(value))


def mul(a: object, b: object) -> BiJet:
    a, b = lift(a), lift(b)
    return BiJet(
        a.c00*b.c00,
        a.c10*b.c00 + a.c00*b.c10,
        a.c01*b.c00 + a.c00*b.c01,
        a.c20*b.c00 + a.c10*b.c10 + a.c00*b.c20,
        a.c11*b.c00 + a.c10*b.c01 + a.c01*b.c10 + a.c00*b.c11,
        a.c02*b.c00 + a.c01*b.c01 + a.c00*b.c02,
    )


def compose(a: object, value: arb, first: arb, second: arb) -> BiJet:
    """Compose a scalar C2 function with a bivariate second-order jet."""
    a = lift(a)
    return BiJet(
        value,
        first*a.c10,
        first*a.c01,
        first*a.c20 + second*a.c10*a.c10/2,
        first*a.c11 + second*a.c10*a.c01,
        first*a.c02 + second*a.c01*a.c01/2,
    )


def unary(a: object, value: arb, first: arb, second: arb) -> BiJet:
    return compose(a, value, first, second)


def inv(a: object) -> BiJet:
    a = lift(a)
    q = 1/a.c00
    return compose(a, q, -q*q, 2*q*q*q)


def sqrt(a: object) -> BiJet:
    a = lift(a)
    root = a.c00.sqrt()
    inv_root = 1/root
    return compose(a, root, inv_root/2, -inv_root**3/4)


def exp(a: object) -> BiJet:
    a = lift(a)
    value = a.c00.exp()
    return compose(a, value, value, value)


def sin(a: object) -> BiJet:
    a = lift(a)
    return compose(a, a.c00.sin(), a.c00.cos(), -a.c00.sin())


def cos(a: object) -> BiJet:
    a = lift(a)
    return compose(a, a.c00.cos(), -a.c00.sin(), -a.c00.cos())


def _scaled_a(z: BiJet) -> BiJet:
    """The scaled I1/z lane, with z-derivatives enclosed to order two."""
    if z.c00.lower() <= 4:
        g0, g1, g2 = g_derivatives(z.c00)
        ez = (-z.c00).exp()
        return compose(z, ez*g0, ez*(g1-g0), ez*(g2-2*g1+g0))
    zl, zh = arb(z.c00.lower()), arb(z.c00.upper())
    a0 = hull((-zh).exp()*zh.bessel_i(1)/zh,
              (-zl).exp()*zl.bessel_i(1)/zl)
    c0 = hull((-zh).exp()*zh.bessel_i(0),
              (-zl).exp()*zl.bessel_i(0))
    a1 = c0/z.c00 - a0 - 2*a0/z.c00
    a2 = 2*a0 - 2*c0/z.c00 + 4*a0/z.c00 - 3*c0/z.c00**2 + 6*a0/z.c00**2
    return compose(z, a0, a1, a2)


def _scaled_b(z: BiJet) -> BiJet:
    """The scaled I2/z^2 lane, with z-derivatives enclosed to order two."""
    if z.c00.lower() <= 4:
        h0, h1, h2 = h_derivatives(z.c00)
        ez = (-z.c00).exp()
        return compose(z, ez*h0, ez*(h1-h0), ez*(h2-2*h1+h0))
    zl, zh = arb(z.c00.lower()), arb(z.c00.upper())
    a0 = hull((-zh).exp()*zh.bessel_i(1)/zh,
              (-zl).exp()*zl.bessel_i(1)/zl)
    c0 = hull((-zh).exp()*zh.bessel_i(0),
              (-zl).exp()*zl.bessel_i(0))
    b0 = hull((-zh).exp()*zl.bessel_i(2)/zl**2,
              (-zl).exp()*zh.bessel_i(2)/zh**2)
    b1 = a0*z.c00/z.c00**2 - 4*c0/z.c00**3 + 8*a0/z.c00**2 - b0
    b2 = (c0/z.c00**2 - 7*a0/z.c00**3 + 20*c0/z.c00**4
          - 40*a0/z.c00**5 - 2*a0/z.c00**2 + 8*c0/z.c00**3
          - 16*a0/z.c00**4 + b0)
    return compose(z, b0, b1, b2)


def parameter_carriers(delta: object, t: object, s: object, alpha: object) -> dict[str, BiJet]:
    """Pointwise raw carriers with delta/t jets and fixed spatial coordinates.

    This is intentionally a pointwise probe, not the spatial K2 integrator.
    It is the smallest executable test of the joint parameter algebra.
    """
    delta, t = lift(delta), lift(t)
    beta = inv(delta)
    beta2 = mul(beta, beta)
    beta_sqrt = sqrt(beta)
    beta32, beta52 = mul(beta, beta_sqrt), mul(beta2, beta_sqrt)
    s, alpha = A(s), A(alpha)
    c, s4 = cos(scale(t, A(1)/4)), sin(scale(t, A(1)/4))
    p, q = A((s/2).sin()**2), A((alpha/2).sin()**2)
    r2 = add(mul(scale(mul(1-p, 1-q), 4), mul(c, c)),
             mul(scale(p*q, 4), mul(s4, s4)))
    radius = sqrt(r2)
    z = scale(mul(beta, radius), 2)
    phase = sub(z, scale(mul(beta, c), 4))
    kernel = mul(scale(beta52, 2), mul(_scaled_a(z), exp(phase)))
    hb = mul(beta32, mul(_scaled_b(z), exp(phase)))
    d = A(2*(1-p-q))
    cc = sub(scale(mul(c, c), 2), 1)
    cs, ca = (s.cos(), alpha.cos())
    n = add(scale(cc, (2*s).cos() + ca*cs), ca*(-1 + cs*cs))
    f = sub(n, mul(d, cc))
    return {
        "muF_main": scale(mul(beta, mul(kernel, f)), 1),
        "nuD_main": mul(scale(beta2, 1), mul(hb, d*d)),
        "nuF_main": mul(mul(beta2, beta), mul(hb, mul(d, f))),
    }


def check() -> None:
    ctx.prec = 120
    d = BiJet(arb("0.05"), arb(1), arb(0))
    t = BiJet(arb("2.9"), arb(0), arb(1))
    out = parameter_carriers(d, t, arb("0.2"), arb("0.3"))
    assert all(getattr(v, field).is_finite() for v in out.values()
               for field in ("c00", "c10", "c01", "c20", "c11", "c02"))
    print("BIVARIATE-JET DESIGN PASS; no K2/G2/G6 promotion")


if __name__ == "__main__":
    check()
