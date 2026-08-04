"""Closed-form feasibility probe for the registered K4 regular-ball route."""

from flint import arb, ctx
import math

T = arb(29) / 10
RHO = arb(7) / 100
R = arb(4)
PHI = 4 * arb.pi()
R_TARGET = arb(59) / 2000
HEADROOM_HALF = arb("0.5") * (1 - arb("0.2758"))


def upper(x):
    return arb(x.upper())


def main():
    ctx.prec = 140
    amplitude = (T / 4).cos()
    # Existing complex-disk construction, reproduced explicitly.
    x = RHO * R**2 / 4
    sinc = (x.sqrt().sinh() / x.sqrt())**2
    p_abs = upper(R**2 / 4 * sinc)
    delta_a = upper(RHO * (2 * p_abs + RHO * p_abs**2 / (amplitude**2)))
    sqrt_mod = upper((1 + delta_a).sqrt())
    # |S| <= 2 sinh(sqrt(rho)*Phi/2)^2/rho on the fixed head.
    s_abs = upper(2 * (RHO.sqrt() * PHI / 2).sinh()**2 / RHO)
    # Four is the carrier's exponential coefficient; this is intentionally
    # a crude modulus, not a claimed production majorant.
    modulus = upper(arb.pi() * PHI * (4 * amplitude * sqrt_mod * s_abs).exp())
    ratio = R_TARGET / RHO
    print("K4 BALL REACH PROBE")
    print("delta_A_upper", delta_a.str(30))
    print("sqrt_mod_upper", sqrt_mod.str(30))
    print("S_head_upper", s_abs.str(30))
    print("M_nuD_crude", modulus.str(30))
    print("target_rho_ratio", ratio.str(30))
    print("headroom_half", HEADROOM_HALF.str(30))
    best = None
    for n in range(0, 17):
        # second derivative Cauchy tail for a degree-n truncation, using the
        # registered conservative coefficient factor.
        tail = upper(modulus * (n + 1) * (n + 2) * ratio**max(n - 1, 0)
                     / (1 - ratio))
        print(f"N={n} tail2={tail.str(30)}")
        if best is None or tail < best[1]:
            best = (n, tail)
    assert best is not None
    status = "PASS" if best[1] < HEADROOM_HALF else "FAIL"
    print("best_N", best[0], "best_tail2", best[1].str(30))
    print("K4 BALL REACH", status)
    print("SCOPE design probe only; no K4/G6 promotion")


if __name__ == "__main__":
    main()
