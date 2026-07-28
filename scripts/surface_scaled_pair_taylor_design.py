"""Bivariate Taylor design for the scaled right-edge pair sum.

This is an interval-stability experiment, not a certificate.  It expands the
exact finite pair identity around a rational beta/lambda centre.  The beta
jet is built from the exact scaled-Bessel derivative recurrence; lambda is
expanded only in the small edge phase.  Keeping the pair minor together is
the important difference from the ordinary Fourier Taylor box.
"""

from __future__ import annotations

from fractions import Fraction
from math import factorial

from flint import arb, ctx

import certify_bulk_beta_taylor_scaled_design as scaled
from probe_surface_scaled_pair_sum import coefficient_tail_bound


def aq(value: Fraction | int | str) -> arb:
    if isinstance(value, Fraction):
        return arb(value.numerator) / value.denominator
    return arb(value)


def vzero(order: int):
    return [arb(0)] * (order + 1)


def vadd(a, b):
    return [a[i] + b[i] for i in range(len(a))]


def vscale(a, c):
    return [value * c for value in a]


def vmul(a, b):
    order = len(a) - 1
    return [sum((a[j] * b[i-j] for j in range(i+1)), arb(0))
            for i in range(order + 1)]


def vinv(a):
    order = len(a) - 1
    out = vzero(order)
    out[0] = 1 / a[0]
    for i in range(1, order + 1):
        out[i] = -sum((a[j] * out[i-j] for j in range(1, i+1)),
                      arb(0)) / a[0]
    return out


def vsincos(z):
    """One-variable Taylor coefficients for sin/cos(z0+h)."""
    order = len(z) - 1
    z0 = z[0]
    dz = list(z)
    dz[0] = arb(0)
    sine, cosine = vzero(order), vzero(order)
    sine[0], cosine[0] = z0.sin(), z0.cos()
    power = vzero(order)
    power[0] = arb(1)
    for index in range(1, order + 1):
        power = vmul(power, dz)
        factor = arb(factorial(index))
        if index % 2:
            sine = vadd(sine, vscale(
                power, ((-1) ** ((index - 1) // 2)) / factor))
        else:
            cosine = vadd(cosine, vscale(
                power, ((-1) ** (index // 2)) / factor))
    return sine, cosine


def pzero(beta_order: int, lambda_order: int):
    return [vzero(beta_order) for _ in range(lambda_order + 1)]


def padd(a, b):
    return [vadd(a[i], b[i]) for i in range(len(a))]


def pscale(a, c):
    return [vscale(value, c) for value in a]


def pmul(a, b):
    """Bivariate truncated product, coefficients divided by factorials."""
    beta_order = len(a[0]) - 1
    lambda_order = len(a) - 1
    out = pzero(beta_order, lambda_order)
    for ell in range(lambda_order + 1):
        for left in range(ell + 1):
            out[ell] = vadd(out[ell], vmul(a[left], b[ell-left]))
    return out


def pfrom(vector, lambda_order):
    return [vector] + [vzero(len(vector) - 1) for _ in range(lambda_order)]


def trig_bivariate(k, x, inv_beta, lambda_order):
    """Return sin(k*(lambda0+h)/beta), cos(...), beta-jet by lambda order."""
    beta_order = len(x) - 1
    sine0, cosine0 = vsincos(vscale(x, arb(k)))
    q = vscale(inv_beta, arb(k))
    powers = [vzero(beta_order) for _ in range(lambda_order + 1)]
    powers[0][0] = arb(1)
    for ell in range(lambda_order):
        powers[ell + 1] = vmul(powers[ell], q)
    sine, cosine = [], []
    for ell in range(lambda_order + 1):
        factor = arb(factorial(ell))
        if ell % 2:
            sine.append(vscale(vmul(cosine0, powers[ell]),
                               ((-1) ** ((ell - 1) // 2)) / factor))
            cosine.append(vscale(vmul(sine0, powers[ell]),
                                 ((-1) ** ((ell - 1) // 2)) / factor))
        else:
            sine.append(vscale(vmul(sine0, powers[ell]),
                               ((-1) ** (ell // 2)) / factor))
            cosine.append(vscale(vmul(cosine0, powers[ell]),
                                 ((-1) ** (ell // 2)) / factor))
    return sine, cosine


def evaluate(poly, beta_radius: arb, lambda_radius: arb) -> arb:
    """Evaluate a truncated polynomial on symmetric beta/lambda boxes."""
    beta_order = len(poly[0]) - 1
    beta_h = beta_radius * arb("0 +/- 1")
    lambda_h = lambda_radius * arb("0 +/- 1")
    lambda_values = []
    for row in poly:
        value = row[-1]
        for coefficient in row[-2::-1]:
            value = value * beta_h + coefficient
        lambda_values.append(value)
    value = lambda_values[-1]
    for coefficient in lambda_values[-2::-1]:
        value = value * lambda_h + coefficient
    return value


def evaluate_swapped(poly, beta_radius: arb, lambda_radius: arb) -> arb:
    """Same box evaluation with the nesting order reversed.

    Arb dependency can differ materially at the moving edge; callers may
    retain the tighter of the two only after proving that both enclose the
    same truncated polynomial.  This remains design-only.
    """
    beta_order = len(poly[0]) - 1
    lambda_order = len(poly) - 1
    beta_h = beta_radius * arb("0 +/- 1")
    lambda_h = lambda_radius * arb("0 +/- 1")
    beta_values = []
    for index in range(beta_order + 1):
        value = poly[lambda_order][index]
        for ell in range(lambda_order - 1, -1, -1):
            value = value * lambda_h + poly[ell][index]
        beta_values.append(value)
    value = beta_values[-1]
    for coefficient in beta_values[-2::-1]:
        value = value * beta_h + coefficient
    return value


def pair_taylor(beta_mid: Fraction, beta_radius: Fraction,
                lambda_mid: Fraction, lambda_radius: Fraction,
                *, modes: int = 120, beta_order: int = 12,
                lambda_order: int = 12, precision: int = 600):
    """Return finite-mode Taylor enclosure plus the explicit mode-tail probe."""
    ctx.prec = precision
    zero_b = vzero(beta_order)
    beta_mid_a = aq(beta_mid)
    beta_jet = [beta_mid_a, arb(1)] + vzero(beta_order - 1)
    inv_beta = vinv(beta_jet)
    # Reuse every scaled Bessel jet.  Without this cache each coefficient
    # recomputed the same shifted Bessel values dozens of times at 600 bits.
    bessel = [scaled.scaled_bessel_jet(m, beta_mid, beta_order)
              for m in range(modes + 2)]
    a_coeff = [zero_b[:] for _ in range(modes + 1)]
    b_coeff = [zero_b[:] for _ in range(modes + 1)]
    for m in range(1, modes + 1):
        # scaled_coefficient_jets returns ordinary derivatives.  The
        # polynomial algebra below stores Taylor coefficients divided by
        # factorial, so convert before multiplying minors.
        jm, jl, jr = bessel[m], bessel[m-1], bessel[m+1]
        jm2 = scaled.bulk.jet_mul(jm, jm, beta_order)
        jl2 = scaled.bulk.jet_mul(jl, jl, beta_order)
        jr2 = scaled.bulk.jet_mul(jr, jr, beta_order)
        qv = [(m-1)*jl2[j] + (m+1)*jr2[j]
              for j in range(beta_order + 1)]
        aj0 = scaled.bulk.jet_mul(jm2, qv, beta_order)
        bj0 = scaled.bulk.jet_mul(jm2, jm2, beta_order)
        aj = [aj0[j] * factorial(j) for j in range(beta_order + 1)]
        bj = [arb(m) * bj0[j] * factorial(j)
              for j in range(beta_order + 1)]
        a_coeff[m] = [aj[j] / arb(factorial(j)) for j in range(beta_order + 1)]
        b_coeff[m] = [bj[j] / arb(factorial(j)) for j in range(beta_order + 1)]
    x = vscale(inv_beta, aq(lambda_mid))
    trigonometric = {
        k: trig_bivariate(k, x, inv_beta, lambda_order)
        for k in range(1, 2 * modes + 1)
    }
    # First collect the beta-polynomial coefficient of each phase frequency.
    # This is algebraically identical to summing pair terms directly, but it
    # avoids repeating the expensive beta convolution for every lambda row of
    # every pair.  The resulting frequency table is only 1..2M.
    frequency = [vzero(beta_order) for _ in range(2 * modes + 1)]
    for m in range(1, modes + 1):
        for n in range(m + 1, modes + 1):
            p, q = n - m, n + m
            minor = vadd(vmul(a_coeff[m], b_coeff[n]),
                         vscale(vmul(a_coeff[n], b_coeff[m]), -1))
            sign = (-1) ** (p + 1)
            frequency[q] = vadd(frequency[q],
                                vscale(minor, sign * (m - n)))
            frequency[p] = vadd(frequency[p],
                                vscale(minor, sign * q))
    total = pzero(beta_order, lambda_order)
    for k in range(1, 2 * modes + 1):
        if not any(frequency[k]):
            continue
        sine, _ = trigonometric[k]
        for ell in range(lambda_order + 1):
            total[ell] = vadd(total[ell], vmul(frequency[k], sine[ell]))
    finite = evaluate(total, aq(beta_radius), aq(lambda_radius))
    beta_box = aq(beta_mid - beta_radius) + (
        aq(beta_radius) * arb("0 +/- 1"))
    tail = coefficient_tail_bound(beta_box, modes)
    return finite, tail, total


def main() -> int:
    import argparse
    parser = argparse.ArgumentParser()
    parser.add_argument("--beta-lo", default="1629/16")
    parser.add_argument("--beta-hi", default="3259/32")
    parser.add_argument("--lambda-lo", default="232/100")
    parser.add_argument("--lambda-hi", default="465/200")
    parser.add_argument("--modes", type=int, default=120)
    parser.add_argument("--beta-order", type=int, default=12)
    parser.add_argument("--lambda-order", type=int, default=12)
    parser.add_argument("--precision", type=int, default=600)
    args = parser.parse_args()
    blo, bhi = Fraction(args.beta_lo), Fraction(args.beta_hi)
    llo, lhi = Fraction(args.lambda_lo), Fraction(args.lambda_hi)
    value, tail, _ = pair_taylor(
        (blo + bhi) / 2, (bhi - blo) / 2,
        (llo + lhi) / 2, (lhi - llo) / 2,
        modes=args.modes, beta_order=args.beta_order,
        lambda_order=args.lambda_order, precision=args.precision)
    print("PAIR TAYLOR DESIGN")
    print("finite", value.str(50))
    print("tail", tail.str(50))
    print("finite_plus_tail", (value + tail * arb("0 +/- 1")).str(50))
    print("SCOPE truncated Taylor only; Taylor remainders and promotion remain open")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
