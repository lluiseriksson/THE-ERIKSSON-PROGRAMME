"""Direct Arb value lane for the repaired main-saddle S2 carrier.

This adapts the campaign's audited linear-exponential integrator to the exact
physical square [0, 6/5]^2. It is design code until parameter boxes and a
manifested residual judge are added.
"""

from __future__ import annotations

from flint import arb

from exp_integrator_arb import (
    A_enclose,
    B_enclose,
    D,
    L_lin,
    V2,
    ball_hi,
    ball_lo,
    hull,
    integrate,
    safe_sqrt,
)


SIDE = arb(6) / 5


class MainSquareV2(V2):
    """V2 geometry with S=(6/5)X instead of S=pi X."""

    def geom(self, X, Y):
        S, A = SIDE * X, SIDE * Y
        P, Q = (S / 2).sin() ** 2, (A / 2).sin() ** 2
        r2 = 4 * (self.c0**2 * (1 - P - Q) + P * Q)
        z = safe_sqrt(4 * self.B**2 * r2)
        return S, A, P, Q, r2, z

    def cell(self, x1, x2, y1, y2, Eb):
        X = hull(arb(x1) / D, arb(x2) / D)
        Y = hull(arb(y1) / D, arb(y2) / D)
        S, A, P, Q, r2, z = self.geom(X, Y)
        Nc, Dd, Nt = self.trig(S, A, Eb)
        af, bf = A_enclose(z), B_enclose(z)
        kslow = 2 * self.B * af
        gslow = self.Gpre * (1 - P - Q) * bf
        area = (
            arb(x2 - x1) / D * arb(y2 - y1) / D * SIDE**2
        )
        if float(ball_hi(z)) < 4:
            core = z.exp() * area
            return (
                core * kslow * Nc,
                core * kslow * Dd,
                core * kslow * Nt,
                core * gslow * Nc,
                core * gslow * Dd,
            )
        xc2, yc2 = x1 + x2, y1 + y2
        Xc, Yc = arb(xc2) / (2 * D), arb(yc2) / (2 * D)
        _, _, _, _, _, zc = self.geom(Xc, Yc)
        radius = safe_sqrt(r2)
        d_r2_x = 4 * (Q - self.c0**2) * (SIDE / 2) * S.sin()
        d_r2_y = 4 * (P - self.c0**2) * (SIDE / 2) * A.sin()
        gx_ball = self.B * d_r2_x / radius
        gy_ball = self.B * d_r2_y / radius
        gx_num = int(round(float(gx_ball.mid()) * 2 * D))
        gy_num = int(round(float(gy_ball.mid()) * 2 * D))
        gx, gy = arb(gx_num) / (2 * D), arb(gy_num) / (2 * D)
        hx, hy = x2 - x1, y2 - y1
        dx = hull(arb(-hx) / (2 * D), arb(hx) / (2 * D))
        dy = hull(arb(-hy) / (2 * D), arb(hy) / (2 * D))
        residual = (gx_ball - gx) * dx + (gy_ball - gy) * dy
        lx, ly = L_lin(gx_num, 2 * hx, 2 * D), L_lin(gy_num, 2 * hy, 2 * D)
        core = zc.exp() * lx * ly * residual.exp() * SIDE**2
        return (
            core * kslow * Nc,
            core * kslow * Dd,
            core * kslow * Nt,
            core * gslow * Nc,
            core * gslow * Dd,
        )


def main_y_point(
    t_q=(29, 10), beta_q=(15, 1), dz1=0.8, dz2=0.15, prec=100
):
    point = MainSquareV2(t_q, beta_q, prec=prec)
    # F=N-C D. The first pass must therefore start at Eb=C; its Nc
    # integral is mu_F, not mu_N. The second pass uses C+mu_F/mu_D.
    first, cells1 = integrate(point, point.C, dzmax=dz1)
    ratio = first[0] / first[1]
    e_num = int(round(float(ratio.mid()) * D))
    ebar_f = arb(e_num) / D
    second, cells2 = integrate(point, point.C + ebar_f, dzmax=dz2)
    knc, kd, _, gnc, gd = second
    s4 = (point.T / 4).sin()
    h_covariance = gnc * kd - knc * gd
    x = -h_covariance / (point.c0 * s4 * kd**2)
    y = point.B * x
    return y, kd, ebar_f, cells1, cells2


def check() -> None:
    y, kd, _, _, _ = main_y_point(dz1=1.0, dz2=0.3, prec=90)
    assert kd > 0
    assert y.is_finite()
    print("direct main-saddle Y value lane finite; design only:", y)


if __name__ == "__main__":
    check()
