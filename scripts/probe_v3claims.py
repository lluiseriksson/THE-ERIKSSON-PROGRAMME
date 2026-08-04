#!/usr/bin/env python3
"""Adversarial check of the two claims that are new in v3 of the paper.

CLAIM A (printed in the lower-bound proof):  rho(T_eps) <= 1 + mu + n*eps, with
that EXACT constant -- not 1+mu+(n-2)eps rounded up, but the bound as written,
and it must hold for every row including the ones outside the pair.

CLAIM B (Remark: Birkhoff is attained at every diameter):  for the 2x2 matrix
[[1,mu],[mu,1]],  Delta = 2 log(1/mu)  and  r = tanh(Delta/4)  EXACTLY.

Same shape and size as the earlier probes (numpy eigh, n <= 12, one process),
which were measured inside the local-light contract.
"""

import math

import numpy as np

CHECKS = 0
BAD = []


def check(name, cond, detail=""):
    global CHECKS
    CHECKS += 1
    if not cond:
        BAD.append(f"{name}: {detail}")
    return bool(cond)


rng = np.random.default_rng(31415)

print("=" * 78)
print("CLAIM A   rho(D_eps M D_eps) <= 1 + mu + n*eps   (exact printed constant)")
print("=" * 78)
print(f"{'n':>3} {'mu':>6} {'eps':>8} {'max row sum':>13} {'1+mu+n*eps':>12} "
      f"{'rho':>11} {'slack':>11}  ok")
worst_slack = float("inf")
for n in (2, 3, 5, 8, 12):
    for mu in (0.05, 0.2, 0.55, 0.9):
        for trial in range(3):
            M = rng.uniform(mu, 1.0, (n, n))
            M = (M + M.T) / 2
            np.fill_diagonal(M, 1.0)
            p, q = 0, min(1, n - 1)
            if n >= 2:
                M[p, q] = M[q, p] = mu          # mu attained at the pair
            for eps in (1.0, 0.3, 1e-2, 1e-5):
                d = np.full(n, eps)
                d[p] = 1.0
                d[q] = 1.0
                T = M * np.outer(d, d)
                rowmax = T.sum(axis=1).max()
                bound = 1 + mu + n * eps
                rho = np.linalg.eigvalsh(T).max()
                check(f"rowsum n={n} mu={mu} eps={eps} t={trial}",
                      rowmax <= bound + 1e-12,
                      f"max row sum {rowmax} > printed bound {bound}")
                check(f"perron n={n} mu={mu} eps={eps} t={trial}",
                      rho <= bound + 1e-12,
                      f"rho {rho} > printed bound {bound}")
                worst_slack = min(worst_slack, bound - rowmax)
                if trial == 0 and eps in (1.0, 1e-2):
                    print(f"{n:>3} {mu:>6.2f} {eps:>8.0e} {rowmax:>13.6f} "
                          f"{bound:>12.6f} {rho:>11.6f} {bound-rowmax:>11.3e}  "
                          f"{'ok' if rowmax <= bound else 'FAIL'}")
print(f"  tightest slack over all cells: {worst_slack:.3e}  (must be >= 0)")

print()
print("=" * 78)
print("CLAIM B   2x2:  Delta = 2 log(1/mu)  and  r = tanh(Delta/4)  exactly")
print("=" * 78)
print(f"{'mu':>8} {'Delta':>12} {'tanh(D/4)':>12} {'r (from eigs)':>15} "
      f"{'|difference|':>13}  ok")
worst_b = 0.0
for mu in (0.02, 0.1, 0.35, 0.5, 0.75, 0.95, 0.999):
    M = np.array([[1.0, mu], [mu, 1.0]])
    # Hilbert diameter, computed from the definition by brute force
    lo, hi = math.inf, -math.inf
    for i in range(2):
        for j in range(2):
            for k in range(2):
                for l in range(2):
                    cr = (M[i, k] * M[j, l]) / (M[j, k] * M[i, l])
                    lo, hi = min(lo, cr), max(hi, cr)
    Delta = math.log(hi)
    ev = np.linalg.eigvalsh(M)
    rho = ev.max()
    sub = max(abs(v) for v in ev if not np.isclose(v, rho))
    r = sub / rho
    tv = math.tanh(Delta / 4)
    check(f"delta mu={mu}", abs(Delta - 2 * math.log(1 / mu)) < 1e-12,
          f"Delta {Delta} != 2log(1/mu) {2*math.log(1/mu)}")
    check(f"attained mu={mu}", abs(r - tv) < 1e-12, f"r {r} != tanh(D/4) {tv}")
    check(f"phi mu={mu}", abs(lo - mu * mu) < 1e-12, f"min cross {lo} != mu^2")
    worst_b = max(worst_b, abs(r - tv))
    print(f"{mu:>8.3f} {Delta:>12.8f} {tv:>12.9f} {r:>15.9f} "
          f"{abs(r-tv):>13.2e}  {'ok' if abs(r-tv) < 1e-12 else 'FAIL'}")
print(f"  worst |r - tanh(Delta/4)| = {worst_b:.2e}  -> equality, not an estimate")

print()
print("-" * 78)
if BAD:
    print(f"{CHECKS} checks -> {len(BAD)} FAILED")
    for b in BAD[:5]:
        print("   ", b)
    raise SystemExit(1)
print(f"{CHECKS} checks -> ALL PASS")
raise SystemExit(0)
