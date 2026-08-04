"""Certified local obstruction to a naive TP2 bridge proof.

The killed kernel is q_beta(u,v)=exp(beta*cos(u-v))-exp(beta*cos(u+v)).
This script certifies one strictly negative 2x2 determinant at beta=3.
It is an obstruction to a global TP2/MLR proof, not a disproof of the
Surface Theorem.
"""

from flint import arb, ctx


def q(beta, u, v):
    return (beta * (u - v).cos()).exp() - (beta * (u + v).cos()).exp()


def main() -> int:
    ctx.prec = 180
    pi = arb.pi()
    beta = arb(3)
    u1, u2 = 3 * pi / 20, 4 * pi / 20
    v1, v2 = 15 * pi / 20, 16 * pi / 20
    det = q(beta, u1, v1) * q(beta, u2, v2) \
        - q(beta, u1, v2) * q(beta, u2, v1)
    assert det.upper() < 0
    print("KILLED VON MISES TP2 OBSTRUCTION PASS")
    print("beta 3; u=3pi/20,4pi/20; v=15pi/20,16pi/20")
    print("det", det.str(80))
    print("SCOPE obstruction only; no Surface-Theorem disproof")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
