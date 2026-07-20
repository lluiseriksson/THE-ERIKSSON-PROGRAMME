"""Explicit beta-derivative majorant for the omitted pair-mode tail.

This is a design helper for the mean-value lane.  It keeps the same positive
geometric ratio as ``coefficient_tail_bound`` and adds (i) coefficient beta
derivatives and (ii) the beta derivative of the small phase
``lambda/beta``.  It carries no gate state by itself.
"""

from __future__ import annotations

from math import comb

from flint import arb

from probe_surface_scaled_pair_sum import _shifted_moment_sums


def tail_beta_derivative_bound(beta: arb, lam: arb, modes: int) -> arb:
    beta_lo, beta_hi = beta.lower(), beta.upper()
    lam_hi = lam.upper()
    m0 = arb(modes + 1)
    ratio = beta_hi / (2 * (m0 + 1))
    q = ratio**4
    j0 = (-beta).exp() * beta.bessel_i(modes + 1)
    sums = _shifted_moment_sums(m0, q)
    # The helper returns S_0,...,S_4; the fifth shifted moment is the
    # standard geometric identity with base moment
    # q(1+26q+66q^2+26q^3+q^4)/(1-q)^6.
    base5 = q*(1 + 26*q + 66*q**2 + 26*q**3 + q**4)/(1-q)**6
    base = [1/(1-q), q/(1-q)**2,
            q*(1+q)/(1-q)**3,
            q*(1+4*q+q**2)/(1-q)**4,
            q*(1+11*q+11*q**2+q**3)/(1-q)**5,
            base5]
    s5 = sum(arb(comb(5, k))*m0**(5-k)*base[k]
             for k in range(6))
    sums.append(s5)
    b_tail = [j0**4 * sums[r+1] for r in range(3)]
    alpha = 2 / beta_lo + beta_hi / (2 * m0 * (m0 + 1))
    gamma = beta_hi / (2 * (m0 + 1))
    a_tail = [j0**4 * (alpha**2 * sums[r+3]
                       + 2 * gamma**2 * sums[r+1])
              for r in range(3)]
    # Finite plus tail moments, using the same positive envelopes as the
    # original mode-tail contract.
    j = [(-beta).exp() * beta.bessel_i(m)
         for m in range(modes + 2)]
    aa = [arb(0)] + [
        j[m]**2 * ((m-1)*j[m-1]**2 + (m+1)*j[m+1]**2)
        for m in range(1, modes + 1)]
    bb = [arb(0)] + [m*j[m]**4 for m in range(1, modes + 1)]
    A = [sum((arb(m)**r*aa[m] for m in range(1, modes+1)), arb(0))
         + a_tail[r] for r in range(3)]
    B = [sum((arb(m)**r*bb[m] for m in range(1, modes+1)), arb(0))
         + b_tail[r] for r in range(3)]
    # L(m)=8*(1+2*(m+1)/beta_lo) is the scaled coefficient derivative
    # majorant.  Apply it to the zeroth and first tail moments.
    c0 = 8*(1 + 2/beta_lo)
    c1 = 16/beta_lo
    ap0, ap1 = c0*a_tail[0] + c1*a_tail[1], c0*a_tail[1] + c1*a_tail[2]
    bp0, bp1 = c0*b_tail[0] + c1*b_tail[1], c0*b_tail[1] + c1*b_tail[2]
    coefficient = 2*(ap0*B[1] + A[0]*bp1 + ap1*B[0] + A[1]*bp0
                    + bp0*A[1] + B[0]*ap1 + bp1*A[0] + B[1]*ap0)
    # |d/d beta T_mn| <= 2(m+n)^2 lambda/beta^2.
    phase = (2*lam_hi/beta_lo**2)*(
        a_tail[0]*B[2] + 2*a_tail[1]*B[1] + a_tail[2]*B[0]
        + b_tail[0]*A[2] + 2*b_tail[1]*A[1] + b_tail[2]*A[0])
    return coefficient + phase
