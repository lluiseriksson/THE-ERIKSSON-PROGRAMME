"""Regular delta=0 geometry for the localized surface remainder.

This removes the two 0/0 expressions in the scaled main chart before
interval evaluation.  It is a K2 building block, not a completed moment or
weighted-judge certificate.
"""

from dataclasses import dataclass
from math import factorial

import mpmath as mp
from flint import arb, ctx

from surface_remainder_arb_jet2 import hull


def square(value: arb) -> arb:
    if value.contains(arb(0)):
        return hull(arb(0), arb(value.abs_upper())**2)
    return value**2


def sinc_squared_y(y: arb, terms: int = 20) -> arb:
    """Enclose sinc(sqrt(y))^2 as an entire series in y."""
    if y.upper() < 0 or (y.lower() < 0 and not y.contains(arb(0))):
        raise ValueError("sinc-squared y must be nonnegative")
    ymax = arb(y.upper())
    total = arb(0)
    for n in range(terms):
        coefficient = arb((-1)**n*2**(2*n+1))/factorial(2*n+2)
        total += coefficient*y**n
    n = terms
    first = arb(2**(2*n+1))/factorial(2*n+2)*ymax**n
    ratio = 4*ymax/arb((2*n+4)*(2*n+3))
    if not ratio < arb(1)/2:
        raise ValueError("sinc-squared tail is not contractive")
    return total+first/(1-ratio)*arb("0 +/- 1")


@dataclass(frozen=True)
class RegularGeometry:
    p_over_delta: arb
    q_over_delta: arb
    w_over_delta: arb
    w: arb
    root: arb
    phase: arb
    inv_z: arb
    d_weight: arb
    f_over_delta: arb


def regular_geometry(delta: arb, t: arb, sigma: arb,
                     tau: arb) -> RegularGeometry:
    """Return the main-chart geometry on a delta box that may contain 0."""
    if delta.upper() < 0 or (delta.lower() < 0 and not delta.contains(arb(0))):
        raise ValueError("delta must be nonnegative")
    sigma2, tau2 = square(sigma), square(tau)
    py, qy = delta*sigma2/4, delta*tau2/4
    p_over = sigma2/4*sinc_squared_y(py)
    q_over = tau2/4*sinc_squared_y(qy)
    c = (t/4).cos()
    c2 = c**2
    w_over = p_over+q_over-delta*p_over*q_over/c2
    w = delta*w_over
    radicand = 1-w
    if not radicand > 0:
        raise ValueError("regular root floor is unresolved")
    root = radicand.sqrt()
    phase = -4*c*w_over/(1+root)
    inv_z = delta/(4*c*root)
    d_weight = 2*(1-delta*(p_over+q_over))
    cc = 2*c2-1
    f_over = -4*p_over*(
        -2*cc*p_over*delta-cc*q_over*delta+2*cc
        +2*p_over*q_over*delta**2-p_over*delta-2*q_over*delta+1
    )
    return RegularGeometry(p_over, q_over, w_over, w, root, phase,
                           inv_z, d_weight, f_over)


def scalar_original(delta: mp.mpf, t: mp.mpf, sigma: mp.mpf,
                    tau: mp.mpf) -> dict[str, mp.mpf]:
    s, alpha = mp.sqrt(delta)*sigma, mp.sqrt(delta)*tau
    c = mp.cos(t/4)
    p, q = mp.sin(s/2)**2, mp.sin(alpha/2)**2
    w = p+q-p*q/c**2
    phase = 4*c/delta*(mp.sqrt(1-w)-1)
    d_weight = 2*(1-p-q)
    cc = 2*c**2-1
    cos_s, cos_a = mp.cos(s), mp.cos(alpha)
    n = cc*mp.cos(2*s)+cos_a*(cc*cos_s-1+cos_s**2)
    return {
        "p_over_delta": p/delta,
        "q_over_delta": q/delta,
        "w_over_delta": w/delta,
        "phase": phase,
        "inv_z": delta/(4*c*mp.sqrt(1-w)),
        "d_weight": d_weight,
        "f_over_delta": (n-cc*d_weight)/delta,
    }


def check() -> None:
    ctx.prec = 160
    mp.mp.dps = 70
    t = arb("2.9")
    geometry = regular_geometry(hull(arb(0), arb(1)/20), t,
                                arb("3.0"), arb("2.0"))
    for delta in (mp.mpf("0.001"), mp.mpf("0.01"), mp.mpf("0.05")):
        exact = scalar_original(delta, mp.mpf("2.9"), mp.mpf(3), mp.mpf(2))
        for name, value in exact.items():
            assert getattr(geometry, name).contains(arb(str(value))), (name, value)
    at_zero = regular_geometry(arb(0), t, arb(3), arb(2))
    c = (t/4).cos(); cc = 2*c**2-1
    assert at_zero.phase.contains(-c*arb(13)/2)
    assert at_zero.f_over_delta.contains(-arb(9)*(2*cc+1))
    assert at_zero.inv_z == 0
    print("regular delta=0 geometry contains all direct positive-delta samples")


if __name__ == "__main__":
    check()
