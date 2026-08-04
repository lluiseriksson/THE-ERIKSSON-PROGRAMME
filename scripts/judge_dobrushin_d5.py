#!/usr/bin/env python3
"""D-5 gates, registered BEFORE any Lean of the volume-family rung.

The rung's claim: for the anisotropic Ising weight on the L x T rectangle
(coupling beta on horizontal nearest neighbours, gamma on vertical, free
boundary, Manhattan distance), the envelope row sums are bounded by the
window 2 tanh|beta| + 2 tanh|gamma| at EVERY site of EVERY rectangle, and
under window <= alpha < 1 the two-point covariance obeys

    |Cov(sigma_p, sigma_q)| <= alpha^dist(p,q) / (1 - alpha),

with alpha and the prefactor fixed BEFORE the volume.  (For +-1 spins each
deltaAt is 2, so the endpoint's delta*delta/4 factor is exactly 1.)

  G15  ROW SUMS OF THE RECTANGLE.  For registered (beta, gamma) cells and
       lattices, every site's sum of tanh|J| is at most the window + 1e-12,
       AND interior sites attain it to 1e-12 -- the geometry is exactly
       2 + 2 bonds inside, fewer on the boundary.
  G16  THE BOUND ITSELF, EXHAUSTIVELY.  Exact Gibbs covariances (full
       enumeration, no sampling) of all single-site spin pairs on small
       rectangles, checked against alpha^d/(1-alpha) with
       alpha = the window.  In-window cells only; every pair must pass.
  G17  UNIFORMITY PROBE.  One cell, one pair (Manhattan distance 2), growing
       volumes: the SAME bound must hold at every volume (the bound never
       hears the volume; the measured covariances must stay under it).

No `assert` anywhere.  Explicit counter; the verdict is refused if fewer
checks ran than expected.  Output printed in full.  Runs on the Colab plane.
"""

import math
import sys
from itertools import product

CHECKS = 0
FAILURES = []


def check(ok, gate, msg):
    global CHECKS
    CHECKS += 1
    tag = "ok " if ok else "FAIL"
    print(f"  [{tag}] {gate}: {msg}")
    if not ok:
        FAILURES.append(f"{gate}: {msg}")


CELLS = [(0.10, 0.10), (0.12, 0.08), (0.05, 0.15)]
G15_LATTICES = [(2, 2), (3, 2), (4, 3), (5, 4)]
G16_LATTICES = [(2, 2), (3, 2), (4, 3)]
G17_LATTICES = [(2, 2), (3, 2), (3, 3), (4, 3)]


def window(beta, gamma):
    return 2.0 * math.tanh(abs(beta)) + 2.0 * math.tanh(abs(gamma))


def sites(L, T):
    return [(a, b) for a in range(L) for b in range(T)]


def bond(p, q, beta, gamma):
    (a, b), (c, d) = p, q
    if abs(a - c) == 1 and b == d:
        return beta
    if a == c and abs(b - d) == 1:
        return gamma
    return 0.0


def dist(p, q):
    return abs(p[0] - q[0]) + abs(p[1] - q[1])


def gate_G15():
    print("G15  row sums of the rectangle: <= window everywhere, = window inside")
    for beta, gamma in CELLS:
        w = window(beta, gamma)
        for L, T in G15_LATTICES:
            ss = sites(L, T)
            sums = {}
            for p in ss:
                sums[p] = sum(math.tanh(abs(bond(p, q, beta, gamma)))
                              for q in ss if q != p)
            worst = max(sums.values())
            check(worst <= w + 1e-12, "G15",
                  f"({beta},{gamma}) {L}x{T}: max row {worst:.12f} <= window {w:.12f}")
            interior = [p for p in ss
                        if 0 < p[0] < L - 1 and 0 < p[1] < T - 1]
            if interior:
                gap = max(abs(sums[p] - w) for p in interior)
                check(gap <= 1e-12, "G15",
                      f"({beta},{gamma}) {L}x{T}: interior attains window, gap {gap:.3e}")
            else:
                below = all(sums[p] < w - 1e-12 for p in ss)
                check(below, "G15",
                      f"({beta},{gamma}) {L}x{T}: no interior; every boundary row strictly below")


def gibbs_covariances(L, T, beta, gamma):
    ss = sites(L, T)
    n = len(ss)
    bonds = []
    for i, p in enumerate(ss):
        for j in range(i + 1, n):
            J = bond(p, ss[j], beta, gamma)
            if J != 0.0:
                bonds.append((i, j, J))
    states = []
    weights = []
    for bits in product((1.0, -1.0), repeat=n):
        e = sum(J * bits[i] * bits[j] for i, j, J in bonds)
        states.append(bits)
        weights.append(math.exp(e))
    Z = sum(weights)
    mean = [sum(wt * st[i] for st, wt in zip(states, weights)) / Z
            for i in range(n)]
    cov = {}
    for i in range(n):
        for j in range(n):
            m2 = sum(wt * st[i] * st[j] for st, wt in zip(states, weights)) / Z
            cov[(i, j)] = m2 - mean[i] * mean[j]
    return ss, cov


def gate_G16():
    print("G16  exact covariances vs alpha^d/(1-alpha), all pairs, exhaustively")
    for beta, gamma in CELLS:
        alpha = window(beta, gamma)
        if not alpha < 1.0:
            check(False, "G16", f"cell ({beta},{gamma}) not in window: {alpha}")
            continue
        for L, T in G16_LATTICES:
            ss, cov = gibbs_covariances(L, T, beta, gamma)
            worst_excess = -1.0
            npairs = 0
            for i, p in enumerate(ss):
                for j, q in enumerate(ss):
                    if i == j:
                        continue
                    npairs += 1
                    bound_ = alpha ** dist(p, q) / (1.0 - alpha)
                    excess = abs(cov[(i, j)]) - bound_
                    worst_excess = max(worst_excess, excess)
            check(worst_excess <= 1e-12, "G16",
                  f"({beta},{gamma}) {L}x{T}: {npairs} pairs, worst |Cov|-bound "
                  f"= {worst_excess:.3e} (<= 0 required)")


def gate_G17():
    print("G17  uniformity probe: one bound, growing volumes")
    beta, gamma = 0.10, 0.10
    alpha = window(beta, gamma)
    bound_ = alpha ** 2 / (1.0 - alpha)
    p, q = (0, 0), (1, 1)
    for L, T in G17_LATTICES:
        ss, cov = gibbs_covariances(L, T, beta, gamma)
        i, j = ss.index(p), ss.index(q)
        c = abs(cov[(i, j)])
        check(c <= bound_ + 1e-15, "G17",
              f"{L}x{T}: |Cov(sigma_(0,0), sigma_(1,1))| = {c:.12f} "
              f"<= {bound_:.12f} (volume-free)")


def main():
    print("judge_dobrushin_d5 -- gates G15/G16/G17 for the volume-family rung")
    print(f"mode: {'optimized' if sys.flags.optimize else 'normal'}")
    print()
    gate_G15()
    print()
    gate_G16()
    print()
    gate_G17()
    print()
    expected = (len(CELLS) * len(G15_LATTICES) * 2
                + len(CELLS) * len(G16_LATTICES)
                + len(G17_LATTICES))
    print(f"checks performed: {CHECKS} (expected {expected})")
    if CHECKS < expected:
        print("VERDICT: FAIL -- fewer checks ran than expected")
        return 1
    if FAILURES:
        print(f"VERDICT: FAIL -- {len(FAILURES)} failure(s):")
        for f in FAILURES:
            print(f"  {f}")
        return 1
    print("VERDICT: PASS -- the rectangle's rows respect the window with "
          "interior attainment, every exhaustive covariance sits under "
          "alpha^d/(1-alpha), and the bound never heard the volume")
    return 0


if __name__ == "__main__":
    sys.exit(main())
