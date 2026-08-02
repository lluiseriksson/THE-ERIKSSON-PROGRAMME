#!/usr/bin/env python3
"""The companion question the submitted paper does NOT answer.

That paper evaluates  sup_{D>0} r(DMD) = (1-mu)/(1+mu),  pinned by Hilbert's
projective diameter, which a positive diagonal congruence cannot move.

The INFIMUM is a different animal and nothing in the paper touches it.  Two
things are known for free:

  * r >= 0 always;
  * rank is a congruence invariant (the rigid half), so if rank M >= 2 then DMD
    always has a nonzero non-Perron eigenvalue -- the ratio cannot BE zero.

Neither of those forbids inf = 0.  This probe asks what actually happens, before
any statement is written down.  Nothing here is a claim; it is reconnaissance.

Question A: is the infimum 0, or bounded away from it?
Question B: if bounded away, by what?  Candidates tested against the measured
            infimum: mu, the diameter, the eigenvalue spread of M, det.

Light-contract: one process, no pool, small n, seconds.
"""

import numpy as np
from scipy.optimize import minimize

rng = np.random.default_rng(11235)


def ratio(T):
    ev = np.linalg.eigvalsh(T)
    rho = ev.max()
    sub = max(abs(v) for v in ev if not np.isclose(v, rho))
    return sub / rho


LOGCAP = 6.0   # r is invariant under a global rescaling of d, so fix the scale
               # and cap the spread; without this Nelder-Mead runs off to
               # overflow and numpy stops converging -- a failure of the probe,
               # not a fact about the infimum.


def r_of_logd(t, M):
    t = np.clip(t - t.mean(), -LOGCAP, LOGCAP)
    d = np.exp(t)
    return ratio(M * np.outer(d, d))


def inf_over_orbit(M, restarts=6):
    n = M.shape[0]
    best = ratio(M)
    for _ in range(restarts):
        t0 = rng.normal(0, 1.0, n)
        res = minimize(r_of_logd, t0, args=(M,), method="Nelder-Mead",
                       options={"maxiter": 4000, "xatol": 1e-10, "fatol": 1e-12})
        best = min(best, res.fun)
    return best


def diameter(M):
    n = M.shape[0]
    hi = -np.inf
    for i in range(n):
        for j in range(n):
            for k in range(n):
                for l in range(n):
                    hi = max(hi, (M[i, k] * M[j, l]) / (M[j, k] * M[i, l]))
    return np.log(hi)


print("=" * 86)
print("QUESTION A: how low can a positive weight push the subdominant ratio?")
print("=" * 86)
print(f"{'n':>3} {'mu':>7} {'r(M)':>10} {'SUP=(1-m)/(1+m)':>16} {'INF found':>11} "
      f"{'lam2/lam1(M)':>13} {'rank':>5}")

rows = []
for n in (3, 4, 5):
    for trial in range(4):
        A = rng.uniform(0.15, 1.0, (n, n))
        M = (A + A.T) / 2
        np.fill_diagonal(M, 1.0)
        mu = min(M[i, j] for i in range(n) for j in range(n) if i != j)
        sup = (1 - mu) / (1 + mu)
        inf = inf_over_orbit(M)
        ev = np.sort(np.linalg.eigvalsh(M))[::-1]
        rank = np.linalg.matrix_rank(M)
        rows.append((n, mu, ratio(M), sup, inf, ev, rank, M))
        print(f"{n:>3} {mu:>7.3f} {ratio(M):>10.6f} {sup:>16.6f} {inf:>11.6f} "
              f"{abs(ev[1])/ev[0]:>13.6f} {rank:>5}")

print()
print("=" * 86)
print("QUESTION B: is the measured infimum tracking any obvious invariant?")
print("=" * 86)
infs = np.array([r[4] for r in rows])
mus = np.array([r[1] for r in rows])
print(f"  smallest infimum seen over all families : {infs.min():.8f}")
print(f"  is any infimum near zero (<1e-3)?        : {bool((infs < 1e-3).any())}")
print()
print(f"{'n':>3} {'INF':>10} {'mu':>8} {'(1-m)/(1+m)':>12} {'|det|^(1/n)':>12} "
      f"{'lam_min/lam_max':>16} {'INF/(lam_min/lam_max)':>22}")
for (n, mu, r0, sup, inf, ev, rank, M) in rows:
    dt = abs(np.linalg.det(M)) ** (1.0 / n)
    spread = ev[-1] / ev[0]
    print(f"{n:>3} {inf:>10.6f} {mu:>8.3f} {sup:>12.6f} {dt:>12.6f} "
          f"{spread:>16.6f} {inf/spread if abs(spread) > 1e-12 else float('nan'):>22.6f}")

print()
print("=" * 86)
print("A pointed case: does concentrating ever HELP?  (M close to rank one)")
print("=" * 86)
for eps in (0.5, 0.1, 0.01):
    n = 4
    u = rng.uniform(0.5, 1.0, n)
    M = np.outer(u, u) + eps * np.eye(n)
    M = M / np.outer(np.sqrt(np.diag(M)), np.sqrt(np.diag(M)))
    mu = min(M[i, j] for i in range(n) for j in range(n) if i != j)
    inf = inf_over_orbit(M)
    print(f"  eps={eps:<6} mu={mu:.4f}  r(M)={ratio(M):.6f}  "
          f"INF={inf:.6f}  SUP={(1-mu)/(1+mu):.6f}")

print()
print("-" * 86)
print("RECONNAISSANCE ONLY.  No statement is claimed from this; it decides")
print("whether there is a theorem here worth pre-registering a judge for.")
