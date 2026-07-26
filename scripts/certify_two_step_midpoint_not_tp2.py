"""Certified obstruction to TP2 for the two-step killed midpoint kernel.

The four-step bridge midpoint uses
    k_beta(u,v) = 4 sum_{m>=1} I_m(beta)^2 sin(m u) sin(m v).
This probe certifies one 2x2 determinant at beta=10.  It is a falsifier for
the tempting midpoint-TP2/MLR proof route only; it does not disprove the
Surface Theorem.
"""

from flint import arb, ctx


def scaled_i(beta: arb, m: int) -> arb:
    return (-beta).exp() * beta.bessel_i(m)


def kernel(beta: arb, u: arb, v: arb, modes: int = 90) -> arb:
    total = arb(0)
    for m in range(1, modes + 1):
        value = scaled_i(beta, m)
        total += 4 * value * value * (m * u).sin() * (m * v).sin()
    k = modes + 1
    ratio = (beta / (2 * (k + 1))) ** 2
    tail = 4 * scaled_i(beta, k) ** 2 / (1 - ratio)
    return total + arb(-1, 1) * tail


def main() -> int:
    ctx.prec = 220
    beta = arb(10)
    pi = arb.pi()
    u1, u2 = 36 * pi / 40, 37 * pi / 40
    v1, v2 = 2 * pi / 40, 3 * pi / 40
    det = (kernel(beta, u1, v1) * kernel(beta, u2, v2)
           - kernel(beta, u1, v2) * kernel(beta, u2, v1))
    assert det.upper() < 0, det
    print("TWO-STEP MIDPOINT TP2 OBSTRUCTION PASS")
    print("beta 10; u=36pi/40,37pi/40; v=2pi/40,3pi/40")
    print("det", det.str(100))
    print("SCOPE obstruction only; no Surface-Theorem disproof")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
