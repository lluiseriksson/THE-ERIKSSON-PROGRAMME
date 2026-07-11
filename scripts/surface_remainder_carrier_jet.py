"""Design check for exact delta-jets of the true moment integrands."""

from __future__ import annotations

import mpmath as mp
from flint import arb, ctx

from surface_remainder_arb_jet2 import Jet2, compose, g_derivatives, h_derivatives, hull


def lift(value: arb) -> Jet2:
    return Jet2(value, arb(0), arb(0))


def add(a: Jet2, b: Jet2) -> Jet2:
    return Jet2(a.c0 + b.c0, a.c1 + b.c1, a.c2 + b.c2)


def neg(a: Jet2) -> Jet2:
    return Jet2(-a.c0, -a.c1, -a.c2)


def mul(a: Jet2, b: Jet2) -> Jet2:
    return Jet2(
        a.c0 * b.c0,
        a.c0 * b.c1 + a.c1 * b.c0,
        a.c0 * b.c2 + a.c1 * b.c1 + a.c2 * b.c0,
    )


def inv(a: Jet2) -> Jet2:
    return Jet2(
        1 / a.c0,
        -a.c1 / a.c0**2,
        a.c1**2 / a.c0**3 - a.c2 / a.c0**2,
    )


def scale(a: Jet2, value: arb) -> Jet2:
    return Jet2(value * a.c0, value * a.c1, value * a.c2)


def sqrt_jet(a: Jet2) -> Jet2:
    root = a.c0.sqrt()
    return Jet2(
        root,
        a.c1 / (2 * root),
        a.c2 / (2 * root) - a.c1**2 / (8 * root**3),
    )


def exp_jet(a: Jet2) -> Jet2:
    value = a.c0.exp()
    return Jet2(value, value * a.c1, value * (a.c2 + a.c1**2 / 2))


def sin_jet(a: Jet2) -> Jet2:
    sine, cosine = a.c0.sin(), a.c0.cos()
    return Jet2(
        sine,
        cosine * a.c1,
        cosine * a.c2 - sine * a.c1**2 / 2,
    )


def cos_jet(a: Jet2) -> Jet2:
    sine, cosine = a.c0.sin(), a.c0.cos()
    return Jet2(
        cosine,
        -sine * a.c1,
        -sine * a.c2 - cosine * a.c1**2 / 2,
    )


def a_scaled_jet(z: Jet2) -> Jet2:
    if z.c0.lower() > 4:
        zl, zh = arb(z.c0.lower()), arb(z.c0.upper())
        a0 = hull((-zh).exp() * zh.bessel_i(1) / zh,
                  (-zl).exp() * zl.bessel_i(1) / zl)
        c0 = hull((-zh).exp() * zh.bessel_i(0),
                  (-zl).exp() * zl.bessel_i(0))
        a1 = c0 / z.c0 - a0 - 2 * a0 / z.c0
        a2 = (
            2 * a0
            - 2 * c0 / z.c0
            + 4 * a0 / z.c0
            - 3 * c0 / z.c0**2
            + 6 * a0 / z.c0**2
        )
        return compose(z, a0, a1, a2)
    g0, g1, g2 = g_derivatives(z.c0)
    ez = (-z.c0).exp()
    return compose(z, ez * g0, ez * (g1 - g0), ez * (g2 - 2 * g1 + g0))


def b_scaled_jet(z: Jet2) -> Jet2:
    if z.c0.lower() > 4:
        zl, zh = arb(z.c0.lower()), arb(z.c0.upper())
        a0 = hull((-zh).exp() * zh.bessel_i(1) / zh,
                  (-zl).exp() * zl.bessel_i(1) / zl)
        c0 = hull((-zh).exp() * zh.bessel_i(0),
                  (-zl).exp() * zl.bessel_i(0))
        c1 = a0 * z.c0
        b0 = hull(
            (-zh).exp() * zl.bessel_i(2) / zl**2,
            (-zl).exp() * zh.bessel_i(2) / zh**2,
        )
        b1 = c1 / z.c0**2 - 4 * c0 / z.c0**3 + 8 * c1 / z.c0**4 - b0
        b2 = (
            c0 / z.c0**2
            - 7 * c1 / z.c0**3
            + 20 * c0 / z.c0**4
            - 40 * c1 / z.c0**5
            - 2 * c1 / z.c0**2
            + 8 * c0 / z.c0**3
            - 16 * c1 / z.c0**4
            + b0
        )
        return compose(z, b0, b1, b2)
    h0, h1, h2 = h_derivatives(z.c0)
    ez = (-z.c0).exp()
    return compose(z, ez * h0, ez * (h1 - h0), ez * (h2 - 2 * h1 + h0))


def as_arb(value: object) -> arb:
    return value if isinstance(value, arb) else arb(str(value))


def carriers(delta_value: object, t_value: object, s_value: object, alpha_value: object) -> dict[str, Jet2]:
    delta = Jet2(as_arb(delta_value), arb(1), arb(0))
    beta = inv(delta)
    beta2 = mul(beta, beta)
    beta_sqrt = sqrt_jet(beta)
    beta32 = mul(beta, beta_sqrt)
    beta52 = mul(beta2, beta_sqrt)
    t, s, alpha = as_arb(t_value), as_arb(s_value), as_arb(alpha_value)
    c, s4 = (t / 4).cos(), (t / 4).sin()
    p = (s / 2).sin() ** 2
    q = (alpha / 2).sin() ** 2
    r2 = 4 * c**2 * (1 - p) * (1 - q) + 4 * s4**2 * p * q
    radius = r2.sqrt()
    z = scale(beta, 2 * radius)
    phase = add(z, neg(scale(beta, 4 * c)))
    kernel = mul(scale(beta52, 2), mul(a_scaled_jet(z), exp_jet(phase)))
    hb = mul(beta32, mul(b_scaled_jet(z), exp_jet(phase)))
    d = 2 * (1 - p - q)
    cc = 2 * c**2 - 1
    n = cc * (2 * s).cos() + alpha.cos() * (cc * s.cos() - 1 + s.cos() ** 2)
    f = n - cc * d
    return {
        "muF_main": scale(mul(beta, kernel), f),
        "nuD_main": scale(mul(beta2, hb), d**2),
        "nuF_main": scale(mul(mul(beta2, beta), hb), d * f),
    }


def scaled_carriers(
    delta_value: object, t_value: object, sigma_value: object, tau_value: object
) -> dict[str, Jet2]:
    """Main carriers after s=sigma*sqrt(delta), including ds da=delta."""

    delta = Jet2(as_arb(delta_value), arb(1), arb(0))
    beta = inv(delta)
    beta2 = mul(beta, beta)
    beta_sqrt = sqrt_jet(beta)
    beta32 = mul(beta, beta_sqrt)
    beta52 = mul(beta2, beta_sqrt)
    root_delta = sqrt_jet(delta)
    sigma, tau = as_arb(sigma_value), as_arb(tau_value)
    s = scale(root_delta, sigma)
    alpha = scale(root_delta, tau)
    t = as_arb(t_value)
    c, s4 = (t / 4).cos(), (t / 4).sin()
    sin_s2, sin_a2 = sin_jet(scale(s, arb(1) / 2)), sin_jet(scale(alpha, arb(1) / 2))
    p, q = mul(sin_s2, sin_s2), mul(sin_a2, sin_a2)
    one = lift(arb(1))
    r2 = add(
        scale(mul(add(one, neg(p)), add(one, neg(q))), 4 * c**2),
        scale(mul(p, q), 4 * s4**2),
    )
    radius = sqrt_jet(r2)
    z = scale(mul(beta, radius), arb(2))
    phase = add(z, neg(scale(beta, 4 * c)))
    kernel_prefactor = mul(scale(beta52, 2), a_scaled_jet(z))
    hb_prefactor = mul(beta32, b_scaled_jet(z))
    d = scale(add(one, neg(add(p, q))), 2)
    cc = 2 * c**2 - 1
    cos_s, cos_a, cos_2s = cos_jet(s), cos_jet(alpha), cos_jet(scale(s, 2))
    n = add(
        scale(cos_2s, cc),
        mul(cos_a, add(scale(cos_s, cc), add(lift(-1), mul(cos_s, cos_s)))),
    )
    f = add(n, neg(scale(d, cc)))
    jacobian = delta
    prefactors = {
        "muF_main": mul(jacobian, mul(beta, mul(kernel_prefactor, f))),
        "nuD_main": mul(jacobian, mul(beta2, mul(hb_prefactor, mul(d, d)))),
        "nuF_main": mul(
            jacobian, mul(mul(beta2, beta), mul(hb_prefactor, mul(d, f)))
        ),
    }
    exponential = exp_jet(phase)
    return {name: mul(prefactor, exponential) for name, prefactor in prefactors.items()}


def scaled_carrier_parts(
    delta_value: object, t_value: object, sigma_value: object, tau_value: object
) -> tuple[dict[str, Jet2], Jet2]:
    """Return non-exponential prefactors and the common phase jet."""

    delta = Jet2(as_arb(delta_value), arb(1), arb(0))
    beta = inv(delta)
    beta2 = mul(beta, beta)
    beta_sqrt = sqrt_jet(beta)
    beta32 = mul(beta, beta_sqrt)
    beta52 = mul(beta2, beta_sqrt)
    root_delta = sqrt_jet(delta)
    sigma, tau = as_arb(sigma_value), as_arb(tau_value)
    s, alpha = scale(root_delta, sigma), scale(root_delta, tau)
    t = as_arb(t_value)
    c, s4 = (t / 4).cos(), (t / 4).sin()
    sin_s2, sin_a2 = sin_jet(scale(s, arb(1) / 2)), sin_jet(scale(alpha, arb(1) / 2))
    p, q = mul(sin_s2, sin_s2), mul(sin_a2, sin_a2)
    one = lift(arb(1))
    r2 = add(
        scale(mul(add(one, neg(p)), add(one, neg(q))), 4 * c**2),
        scale(mul(p, q), 4 * s4**2),
    )
    radius = sqrt_jet(r2)
    z = scale(mul(beta, radius), arb(2))
    phase = add(z, neg(scale(beta, 4 * c)))
    kernel_prefactor = mul(scale(beta52, 2), a_scaled_jet(z))
    hb_prefactor = mul(beta32, b_scaled_jet(z))
    d = scale(add(one, neg(add(p, q))), 2)
    cc = 2 * c**2 - 1
    cos_s, cos_a, cos_2s = cos_jet(s), cos_jet(alpha), cos_jet(scale(s, 2))
    n = add(
        scale(cos_2s, cc),
        mul(cos_a, add(scale(cos_s, cc), add(lift(-1), mul(cos_s, cos_s)))),
    )
    f = add(n, neg(scale(d, cc)))
    return {
        "muF_main": mul(delta, mul(beta, mul(kernel_prefactor, f))),
        "nuD_main": mul(delta, mul(beta2, mul(hb_prefactor, mul(d, d)))),
        "nuF_main": mul(
            delta, mul(mul(beta2, beta), mul(hb_prefactor, mul(d, f)))
        ),
    }, phase


def scalar_carrier(delta: mp.mpf, t: mp.mpf, s: mp.mpf, alpha: mp.mpf, name: str) -> mp.mpf:
    beta = 1 / delta
    c, s4 = mp.cos(t / 4), mp.sin(t / 4)
    p, q = mp.sin(s / 2) ** 2, mp.sin(alpha / 2) ** 2
    r2 = 4 * c**2 * (1 - p) * (1 - q) + 4 * s4**2 * p * q
    radius = mp.sqrt(r2)
    z, zs = 2 * beta * radius, 4 * beta * c
    kernel = 2 * beta ** mp.mpf("2.5") * (mp.besseli(1, z) / z) * mp.exp(-zs)
    hb = beta ** mp.mpf("1.5") * (mp.besseli(2, z) / z**2) * mp.exp(-zs)
    d = 2 * (1 - p - q)
    cc = 2 * c**2 - 1
    n = cc * mp.cos(2 * s) + mp.cos(alpha) * (cc * mp.cos(s) - 1 + mp.cos(s) ** 2)
    f = n - cc * d
    return {
        "muF_main": beta * kernel * f,
        "nuD_main": beta**2 * hb * d**2,
        "nuF_main": beta**3 * hb * d * f,
    }[name]


def check() -> None:
    ctx.prec = 180
    mp.mp.dps = 70
    point = (mp.mpf(1) / 30, mp.mpf("2.9"), mp.mpf("0.4"), mp.mpf("0.7"))
    jets = carriers(*(str(value) for value in point))
    for name, jet in jets.items():
        expected = mp.diff(lambda d: scalar_carrier(d, *point[1:], name), point[0], 2) / 2
        assert jet.c2.contains(arb(str(expected))), (name, jet.c2, expected)
    delta_box = hull(arb("0.06"), arb(1) / 15)
    spatial_box = hull(arb(0), arb("0.01"))
    interval_jets = carriers(delta_box, arb("2.9"), spatial_box, spatial_box)
    assert all(jet.c2.is_finite() for jet in interval_jets.values())
    scaled = scaled_carriers(str(point[0]), str(point[1]), "1.2", "2.1")
    s_value, a_value = point[0].sqrt() * mp.mpf("1.2"), point[0].sqrt() * mp.mpf("2.1")
    for name, jet in scaled.items():
        expected = mp.diff(
            lambda d: d
            * scalar_carrier(
                d,
                point[1],
                mp.sqrt(d) * mp.mpf("1.2"),
                mp.sqrt(d) * mp.mpf("2.1"),
                name,
            ),
            point[0],
            2,
        ) / 2
        assert jet.c2.contains(arb(str(expected))), (name, jet.c2, expected)
    print("true-integrand delta jets contain mpmath second derivatives")


if __name__ == "__main__":
    check()
