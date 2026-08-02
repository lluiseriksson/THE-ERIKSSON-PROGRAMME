#!/usr/bin/env python3
"""GATE JA (pre-registered in docs/congruence/STABILISER-CHARTER.md).

MONOTONE, adversarially.  S is not drawn uniformly; every family below is built
to TRY to increase the diameter.  Registered prediction, before running:

    Delta(S M S^T) - Delta(M) <= 1e-9  in EVERY cell.

One strict increase kills MONOTONE as stated.
"""
import itertools, math, sys
import numpy as np

rng = np.random.default_rng(4242)
CHECKS = 0
BAD = []


def check(name, cond, detail=""):
    global CHECKS
    CHECKS += 1
    if not cond:
        BAD.append(f"{name}: {detail}")


def diameter(M):
    n = M.shape[0]
    hi = -math.inf
    for i, j, k, l in itertools.product(range(n), repeat=4):
        den = M[j, k] * M[i, l]
        if den <= 0 or not np.isfinite(den):
            return math.inf
        v = (M[i, k] * M[j, l]) / den
        if not np.isfinite(v):
            return math.inf
        hi = max(hi, v)
    return math.log(hi)


def rand_M(n, mu_small=False):
    lo = 1e-3 if mu_small else 0.2
    A = rng.uniform(lo, 1.0, (n, n))
    M = (A + A.T) / 2
    np.fill_diagonal(M, 1.0)
    return M


families = {}
def fam(name):
    def deco(f):
        families[name] = f
        return f
    return deco


@fam("near-singular S")
def _(n):
    u = rng.uniform(0.2, 1.0, n)
    return np.outer(u, u) + 1e-6 * rng.uniform(0.1, 1.0, (n, n))


@fam("rows differing by 1e4")
def _(n):
    S = rng.uniform(0.2, 1.0, (n, n))
    scale = np.logspace(0, 4, n)
    rng.shuffle(scale)
    return S * scale[:, None]


@fam("one dominant entry")
def _(n):
    S = rng.uniform(0.05, 0.2, (n, n))
    S[rng.integers(n), rng.integers(n)] = 1e5
    return S


@fam("near-monomial + tiny mixing")
def _(n):
    d = rng.uniform(0.5, 2.0, n)
    P = np.eye(n)[rng.permutation(n)]
    return np.diag(d) @ P + 1e-8 * rng.uniform(0.5, 1.0, (n, n))


@fam("columns nearly proportional")
def _(n):
    v = rng.uniform(0.3, 1.0, n)
    return np.outer(v, rng.uniform(0.5, 1.5, n)) + 1e-4 * rng.uniform(0.1, 1.0, (n, n))


print("=" * 90)
print("GATE JA -- adversarial MONOTONE.  Registered prediction: max gap <= 1e-9")
print("=" * 90)
print(f"{'family':>28} {'n':>3} {'cells':>6} {'max Delta(SMS^T)-Delta(M)':>27} {'verdict':>9}")
worst_overall = -math.inf
for name, build in families.items():
    for n in (3, 5, 8):
        worst = -math.inf
        cells = 0
        for t in range(40):
            M = rand_M(n, mu_small=(t % 2 == 0))
            S = build(n)
            T = S @ M @ S.T
            if (T <= 0).any() or not np.isfinite(T).all():
                continue
            dM, dT = diameter(M), diameter(T)
            if not (np.isfinite(dM) and np.isfinite(dT)):
                continue
            cells += 1
            gap = dT - dM
            worst = max(worst, gap)
            check(f"{name} n={n} t={t}", gap <= 1e-9, f"gap={gap}")
        worst_overall = max(worst_overall, worst)
        print(f"{name:>28} {n:>3} {cells:>6} {worst:>27.3e} "
              f"{'ok' if worst <= 1e-9 else 'FAIL':>9}")

print("-" * 90)
print(f"worst gap over every adversarial cell: {worst_overall:.3e}")
print(f"{CHECKS} checks -> " + ("ALL PASS, JA holds" if not BAD else f"{len(BAD)} FAILED"))
for b in BAD[:5]:
    print("   ", b)
sys.exit(1 if BAD else 0)
