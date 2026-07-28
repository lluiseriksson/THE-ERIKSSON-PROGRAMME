"""Direct Arb value lane for the repaired main-saddle S2 carrier.

This adapts the campaign's audited linear-exponential integrator to the exact
physical square [0, 6/5]^2. It is design code until parameter boxes and a
manifested residual judge are added.
"""

from __future__ import annotations

import heapq

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


def integrate_targeted(
    point: MainSquareV2,
    ebar: arb,
    scales: tuple[float, float, float, float, float],
    dzmax: float = 0.3,
    max_cells: int = 100000,
    hmin: int = 30,
):
    """Mandatory z refinement followed by covariance-width refinement."""

    heap = []
    serial = 0

    def push(x1: int, x2: int, y1: int, y2: int) -> None:
        nonlocal serial
        X = hull(arb(x1) / D, arb(x2) / D)
        Y = hull(arb(y1) / D, arb(y2) / D)
        z = point.geom(X, Y)[-1]
        dz = float(ball_hi(z)) - float(ball_lo(z))
        if dz > dzmax and (x2 - x1) > hmin:
            xm, ym = (x1 + x2) // 2, (y1 + y2) // 2
            push(x1, xm, y1, ym)
            push(xm, x2, y1, ym)
            push(x1, xm, ym, y2)
            push(xm, x2, ym, y2)
            return
        values = point.cell(x1, x2, y1, y2, ebar)
        score = max(
            float(value.rad()) / max(scale, 1e-300)
            for value, scale in zip(values, scales)
        )
        heapq.heappush(
            heap, (-score, serial, x1, x2, y1, y2, values)
        )
        serial += 1

    push(0, D, 0, D)
    while len(heap) + 3 <= max_cells:
        _, _, x1, x2, y1, y2, _ = heapq.heappop(heap)
        if x2 - x1 <= hmin:
            # At the floor, preserve the cell and stop if it is the widest.
            values = point.cell(x1, x2, y1, y2, ebar)
            heapq.heappush(heap, (0.0, serial, x1, x2, y1, y2, values))
            serial += 1
            break
        xm, ym = (x1 + x2) // 2, (y1 + y2) // 2
        push(x1, xm, y1, ym)
        push(xm, x2, y1, ym)
        push(x1, xm, ym, y2)
        push(xm, x2, ym, y2)
    totals = [arb(0)] * 5
    for *_, values in heap:
        for index, value in enumerate(values):
            totals[index] += value
    return totals, len(heap)


def main_y_point(
    t_q=(29, 10), beta_q=(15, 1), dz1=0.8, dz2=0.15, prec=100,
    targeted_cells: int | None = None,
):
    point = MainSquareV2(t_q, beta_q, prec=prec)
    # F=N-C D. The first pass must therefore start at Eb=C; its Nc
    # integral is mu_F, not mu_N. The second pass uses C+mu_F/mu_D.
    first, cells1 = integrate(point, point.C, dzmax=dz1)
    ratio = first[0] / first[1]
    e_num = int(round(float(ratio.mid()) * D))
    ebar_f = arb(e_num) / D
    total_ebar = point.C + ebar_f
    if targeted_cells is None:
        second, cells2 = integrate(point, total_ebar, dzmax=dz2)
    else:
        pilot, _ = integrate(point, total_ebar, dzmax=max(dz2, 0.3))
        kd_scale = max(abs(float(pilot[1].mid())), 1e-300)
        gd_scale = max(abs(float(pilot[4].mid())), 1e-300)
        scales = (kd_scale, kd_scale, kd_scale, gd_scale, gd_scale)
        second, cells2 = integrate_targeted(
            point,
            total_ebar,
            scales,
            dzmax=max(dz2, 0.3),
            max_cells=targeted_cells,
        )
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
