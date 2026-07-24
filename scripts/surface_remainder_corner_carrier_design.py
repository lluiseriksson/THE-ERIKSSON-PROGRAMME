"""Design-only corner chart for the K4 carrier.

The scaled representation uses ``exp(z)`` and ``sqrt(R^2)`` separately.  At
the geometric zero set this creates interval singularities even though the
product has the exact identity

``exp(-z) I_n(z)/z^n * exp(z-4 beta c) = exp(-4 beta c) I_n(z)/z^n``.

This module evaluates the right-hand side as a power series in
``u=(beta R)^2/4``.  It is a design probe only: the finite series below has no
production tail contract and must not enter a gate or manifest.
"""

from math import factorial

from flint import arb

from surface_remainder_centered_prefactor import (
    Dual,
    Jet,
    dual,
    jet,
    jadd,
    jexp,
    jinv,
    jmul,
    jneg,
    jscale,
    jsin,
    jsquare,
    jcos,
    jsqrt,
)
from surface_remainder_tjet import TJet, tjet


TERMS = 80


def jet2_factorized_carriers(delta_value, t_value, s_value, alpha_value,
                              mirror: bool = False):
    """Design-only fixed-physical ``Jet2`` carrier adapter.

    This is the algebraic corner route in the two-delta-derivative algebra
    used by the K4 smoke.  It intentionally has no production tail contract.
    """
    from surface_remainder_arb_jet2 import Jet2
    from surface_remainder_carrier_jet import (
        exp_jet as j2exp, inv as j2inv, lift as j2lift, mul as j2mul,
        scale as j2scale, sqrt_jet as j2sqrt,
    )
    delta = Jet2(arb(str(delta_value)), arb(1), arb(0))
    beta = j2inv(delta)
    beta2 = j2mul(beta, beta)
    beta_sqrt = j2sqrt(beta)
    beta32, beta52 = j2mul(beta, beta_sqrt), j2mul(beta2, beta_sqrt)
    t, s, alpha = arb(str(t_value)), arb(str(s_value)), arb(str(alpha_value))
    c, s4 = (t / 4).cos(), (t / 4).sin()
    if mirror:
        ps, pa, reference = (s / 2).cos() ** 2, (alpha / 2).cos() ** 2, s4
    else:
        ps, pa, reference = (s / 2).sin() ** 2, (alpha / 2).sin() ** 2, c
    r2 = 4 * c**2 * (1 - ps) * (1 - pa) + 4 * s4**2 * ps * pa
    # The Bessel quotients are entire in u=(beta*R)^2/4.
    u = j2scale(j2scale(beta2, r2), arb(1) / 4)
    ra = j2_ratio_series(u, "A")
    rb = j2_ratio_series(u, "B")
    fixed = j2exp(j2scale(beta, -4 * reference))
    kernel = j2mul(j2scale(j2mul(beta52, ra), 2), fixed)
    hkernel = j2mul(j2mul(beta32, rb), fixed)
    d = 2 * (1 - ps - pa)
    cc = 2 * c**2 - 1
    cos_s = -s.cos() if mirror else s.cos()
    cos_a = -alpha.cos() if mirror else alpha.cos()
    f = (cos_s - 1) * ((2 * cos_s + 1) * cc + cos_a * (cos_s + 1 + cc))
    if mirror:
        return {"MD_mirror": j2scale(j2mul(kernel, j2lift(d)), 1),
                "MF_mirror": j2scale(j2mul(kernel, j2lift(f)), 1),
                "MD2r_mirror": j2mul(beta2, j2mul(hkernel, j2lift(d*d))),
                "MDFr_mirror": j2mul(beta2, j2mul(hkernel, j2lift(d*f)))}
    return {"muF_main": j2mul(beta, j2mul(kernel, j2lift(f))),
            "nuD_main": j2mul(beta2, j2mul(hkernel, j2lift(d*d))),
            "nuF_main": j2mul(j2mul(beta2, beta), j2mul(hkernel, j2lift(d*f)))}


def j2_ratio_series(u, family: str):
    """Finite positive series in ``u`` for the Jet2 diagnostic adapter."""
    from surface_remainder_carrier_jet import add, lift, mul, scale
    out, power = lift(0), lift(1)
    for k in range(TERMS):
        if family == "A":
            coefficient = arb(1) / (2 * factorial(k) * factorial(k + 1))
        elif family == "B":
            coefficient = arb(1) / (4 * factorial(k) * factorial(k + 2))
        else:
            raise ValueError(family)
        out = add(out, scale(power, coefficient))
        power = mul(power, u)
    return add(out, _compose_tail_jet2(u, family))


def _compose_tail_jet2(u, family: str):
    """Outward second-order Taylor enclosure of the positive omitted tail."""
    from surface_remainder_arb_jet2 import Jet2
    from surface_remainder_carrier_jet import lift
    upper = arb(u.c0.upper())
    if upper < 0:
        upper = arb(0)
    b0, b1, b2, *_ = ratio_tail_majorants(upper, family, TERMS, 4)
    sign = arb("0 +/- 1")
    return Jet2(b0 * sign, b1 * arb(u.c1.abs_upper()) * sign,
                (b1 * arb(u.c2.abs_upper())
                 + b2 * arb(u.c1.abs_upper())**2) * sign)


def ratio_tail_majorants(u_upper, family: str, terms: int = TERMS,
                         order: int = 4):
    """Positive coefficient tail bounds for d^j/du^j of I_n(z)/z^n.

    This is a scalar design lemma.  For ``0 <= u <= u_upper`` and each
    derivative order ``j`` the first omitted term is divided by ``1-q_j``.
    It does not by itself bound delta derivatives of ``u(delta)`` and is
    therefore not a production Jet certificate.
    """
    U = arb(u_upper)
    if U < 0 or terms <= 0 or order < 0:
        raise ValueError("invalid tail domain")
    out = []
    for j in range(order + 1):
        k = max(terms, j)
        if family == "A":
            coefficient = arb(1) / (2 * factorial(k) * factorial(k + 1))
            denominator_shift = k + 2
        elif family == "B":
            coefficient = arb(1) / (4 * factorial(k) * factorial(k + 2))
            denominator_shift = k + 3
        else:
            raise ValueError(family)
        falling = factorial(k) // factorial(k - j)
        first = coefficient * falling * U ** (k - j)
        q = U / (denominator_shift * (k + 1 - j))
        if not q < 1:
            raise ValueError("tail ratio is not contractive")
        out.append(first / (1 - q))
    return out


def _compose_tail_tjet(u: TJet, family: str) -> TJet:
    """Chain the scalar positive tail through a fourth-order TJet."""
    upper = arb(u.v.upper())
    if upper < 0:
        upper = arb(0)
    bounds = ratio_tail_majorants(upper, family, TERMS, 4)
    a1, a2, a3, a4 = (arb(u.d.abs_upper()), arb(u.d2.abs_upper()),
                       arb(u.d3.abs_upper()), arb(u.d4.abs_upper()))
    b0, b1, b2, b3, b4 = bounds
    c0 = b0
    c1 = b1*a1
    c2 = b2*a1**2 + b1*a2
    c3 = b3*a1**3 + 3*b2*a1*a2 + b1*a3
    c4 = b4*a1**4 + 6*b3*a1**2*a2 + 3*b2*a2**2 + 4*b2*a1*a3 + b1*a4
    sign = arb("0 +/- 1")
    return tjet(arb(0), c1*sign, c2*sign, c3*sign, c4*sign) + tjet(c0*sign)


def _ratio_series(u: Jet, family: str) -> Jet:
    out = jet(0)
    power = jet(1)
    for k in range(TERMS):
        if family == "A":
            coefficient = arb(1) / (
                2 * factorial(k) * factorial(k + 1)
            )
        elif family == "B":
            coefficient = arb(1) / (
                4 * factorial(k) * factorial(k + 2)
            )
        else:
            raise ValueError(family)
        out = jadd(out, jscale(power, coefficient))
        power = jmul(power, u)
    return out


def _factorized(delta_value, t_value, sigma, tau, mirror: bool):
    delta = Jet(dual(delta_value), dual(1), dual(0))
    beta = jinv(delta)
    beta2 = jsquare(beta)
    beta_sqrt = jsqrt(beta)
    beta32 = jmul(beta, beta_sqrt)
    beta52 = jmul(beta2, beta_sqrt)
    s, alpha = jscale(jsqrt(delta), sigma), jscale(jsqrt(delta), tau)
    t = t_value
    c, s4 = (t / 4).cos(), (t / 4).sin()
    if mirror:
        ps = jsquare(jcos(jscale(s, arb(1) / 2)))
        pa = jsquare(jcos(jscale(alpha, arb(1) / 2)))
        reference = s4
    else:
        ps = jsquare(jsin(jscale(s, arb(1) / 2)))
        pa = jsquare(jsin(jscale(alpha, arb(1) / 2)))
        reference = c
    one = jet(1)
    r2 = jadd(
        jscale(jmul(jadd(one, jneg(ps)), jadd(one, jneg(pa))), 4 * c**2),
        jscale(jmul(ps, pa), 4 * s4**2),
    )
    # No sqrt: u=(beta R)^2/4=beta^2 R^2/4 is polynomial in the chart.
    u = jscale(jmul(beta2, r2), arb(1) / 4)
    ratio_a, ratio_b = _ratio_series(u, "A"), _ratio_series(u, "B")
    fixed_exp = jexp(jscale(beta, -4 * reference))
    kernel = jmul(jscale(jmul(beta52, ratio_a), 2), fixed_exp)
    hkernel = jmul(jmul(beta32, ratio_b), fixed_exp)
    d = jscale(jadd(one, jneg(jadd(ps, pa))), 2)
    cc = 2 * c**2 - 1
    cos_s = jneg(jcos(s)) if mirror else jcos(s)
    cos_a = jneg(jcos(alpha)) if mirror else jcos(alpha)
    f = jmul(
        jadd(cos_s, jet(-1)),
        jadd(
            jscale(jadd(jscale(cos_s, 2), jet(1)), cc),
            jmul(cos_a, jadd(cos_s, jadd(jet(1), jet(cc)))),
        ),
    )
    if mirror:
        return {
            "MD_mirror": jmul(kernel, d),
            "MF_mirror": jmul(kernel, f),
            "MD2r_mirror": jmul(beta2, jmul(hkernel, jsquare(d))),
            "MDFr_mirror": jmul(beta2, jmul(hkernel, jmul(d, f))),
        }
    return {
        "muF_main": jmul(beta, jmul(kernel, f)),
        "nuD_main": jmul(beta2, jmul(hkernel, jsquare(d))),
        "nuF_main": jmul(jmul(beta2, beta), jmul(hkernel, jmul(d, f))),
    }


def coefficient(delta_value, t_value, sigma: Dual, tau: Dual):
    return _factorized(delta_value, t_value, sigma, tau, False)


def mirror_coefficient(delta_value, t_value, sigma: Dual, tau: Dual):
    return _factorized(delta_value, t_value, sigma, tau, True)


def physical_carriers(delta_value, t_value, s: Dual, alpha: Dual,
                      mirror: bool = False):
    """Same factorized identity in fixed physical coordinates (design only)."""
    delta = Jet(dual(delta_value), dual(1), dual(0))
    beta = jinv(delta)
    beta2 = jsquare(beta)
    beta_sqrt = jsqrt(beta)
    beta32 = jmul(beta, beta_sqrt)
    beta52 = jmul(beta2, beta_sqrt)
    sj, aj = jet(s), jet(alpha)
    t = t_value
    c, s4 = (t / 4).cos(), (t / 4).sin()
    if mirror:
        ps, pa, reference = jsquare(jcos(jscale(sj, arb(1)/2))), jsquare(jcos(jscale(aj, arb(1)/2))), s4
    else:
        ps, pa, reference = jsquare(jsin(jscale(sj, arb(1)/2))), jsquare(jsin(jscale(aj, arb(1)/2))), c
    one = jet(1)
    r2 = jadd(jscale(jmul(jadd(one, jneg(ps)), jadd(one, jneg(pa))), 4*c**2),
              jscale(jmul(ps, pa), 4*s4**2))
    u = jscale(jmul(beta2, r2), arb(1) / 4)
    ra, rb = _ratio_series(u, "A"), _ratio_series(u, "B")
    fixed_exp = jexp(jscale(beta, -4*reference))
    kernel = jmul(jscale(jmul(beta52, ra), 2), fixed_exp)
    hkernel = jmul(jmul(beta32, rb), fixed_exp)
    d = jscale(jadd(one, jneg(jadd(ps, pa))), 2)
    cc = 2*c**2-1
    cos_s = jneg(jcos(sj)) if mirror else jcos(sj)
    cos_a = jneg(jcos(aj)) if mirror else jcos(aj)
    f = jmul(jadd(cos_s, jet(-1)),
             jadd(jscale(jadd(jscale(cos_s,2),jet(1)),cc),
                  jmul(cos_a,jadd(cos_s,jadd(jet(1),jet(cc))))))
    if mirror:
        return {"MD_mirror":jmul(kernel,d),"MF_mirror":jmul(kernel,f),
                "MD2r_mirror":jmul(beta2,jmul(hkernel,jsquare(d))),
                "MDFr_mirror":jmul(beta2,jmul(hkernel,jmul(d,f)))}
    return {"muF_main":jmul(beta,jmul(kernel,f)),
            "nuD_main":jmul(beta2,jmul(hkernel,jsquare(d))),
            "nuF_main":jmul(jmul(beta2,beta),jmul(hkernel,jmul(d,f)))}


def _ratio_series_tjet(u: TJet, family: str) -> TJet:
    """Finite diagnostic series in the production fourth-order t algebra."""
    out, power = tjet(0), tjet(1)
    for k in range(TERMS):
        if family == "A":
            coefficient = arb(1) / (2 * factorial(k) * factorial(k + 1))
        elif family == "B":
            coefficient = arb(1) / (4 * factorial(k) * factorial(k + 2))
        else:
            raise ValueError(family)
        out += coefficient * power
        power *= u
    # The finite polynomial is followed by an outward chain-rule enclosure
    # for the positive omitted tail.  This remains design-only because the
    # enclosing domain and all outer-carrier contracts are still incomplete.
    return out + _compose_tail_tjet(u, family)


def tjet_carriers(delta_value, t_value, s_value, alpha_value,
                  mirror: bool = False):
    """Design-only TJet adapter; no tail contract and never a gate input."""
    delta = delta_value if isinstance(delta_value, TJet) else tjet(delta_value)
    beta, beta2 = 1 / delta, (1 / delta) ** 2
    beta_sqrt = delta.sqrt().inv()
    beta32, beta52 = beta * beta_sqrt, beta2 * beta_sqrt
    t = t_value if isinstance(t_value, TJet) else tjet(t_value)
    s, alpha = (s_value if isinstance(s_value, arb) else arb(str(s_value))), (alpha_value if isinstance(alpha_value, arb) else arb(str(alpha_value)))
    c, s4 = (t / 4).cos(), (t / 4).sin()
    if mirror:
        ps, pa, reference = (s/2).cos()**2, (alpha/2).cos()**2, s4
    else:
        ps, pa, reference = (s/2).sin()**2, (alpha/2).sin()**2, c
    one = tjet(1)
    r2 = 4*c**2*(one-ps)*(one-pa) + 4*s4**2*ps*pa
    # The Bessel quotients are entire in u=(beta*R)^2/4.
    u = beta2 * r2 / 4
    ra, rb = _ratio_series_tjet(u, "A"), _ratio_series_tjet(u, "B")
    fixed_exp = (-4 * beta * reference).exp()
    kernel, hkernel = 2*beta52*ra*fixed_exp, beta32*rb*fixed_exp
    d = 2*(one-ps-pa)
    cc = 2*c**2 - 1
    cos_s = -s.cos() if mirror else s.cos()
    cos_a = -alpha.cos() if mirror else alpha.cos()
    f = (cos_s-1) * ((2*cos_s+1)*cc + cos_a*(cos_s+1+cc))
    if mirror:
        return {"MD_mirror": kernel*d, "MF_mirror": kernel*f,
                "MD2r_mirror": beta2*hkernel*d**2,
                "MDFr_mirror": beta2*hkernel*d*f}
    return {"muF_main": beta*kernel*f, "nuD_main": beta2*hkernel*d**2,
            "nuF_main": beta2*beta*hkernel*d*f}
