#!/usr/bin/env python3
"""Which congruences preserve Hilbert's projective diameter?

The submitted paper proves Delta(DMD) = Delta(M) for D positive diagonal, and
that is the whole mechanism: a positive weight moves the spectrum but cannot
move the geometry.  Section 8 leaves open what happens for congruences by
positive matrices that are NOT diagonal, "where the cross-ratio no longer
cancels".

Reconnaissance for two candidate statements, neither claimed:

  (MONOTONE)  Delta(S M S^T) <= Delta(M) for every entrywise positive S.
              i.e. a genuinely mixing congruence can only CONTRACT the
              projective geometry, never expand it.

  (STABILISER) equality holds exactly when S is monomial -- a positive diagonal
              times a permutation.  That would say the diagonal group is
              precisely the stabiliser of the obstruction, so nothing larger
              inherits the fusion bound.

Sanity checks first: diagonal and permutation S must come out exactly equal, or
the probe is measuring its own bug.
"""

import itertools
import math

import numpy as np

rng = np.random.default_rng(90210)


def diameter(M):
    n = M.shape[0]
    hi = -math.inf
    for i, j, k, l in itertools.product(range(n), repeat=4):
        den = M[j, k] * M[i, l]
        if den <= 0:
            return math.inf
        hi = max(hi, (M[i, k] * M[j, l]) / den)
    return math.log(hi)


def unit_diag(M):
    d = np.sqrt(np.diag(M))
    return M / np.outer(d, d)


def rand_M(n):
    A = rng.uniform(0.2, 1.0, (n, n))
    M = (A + A.T) / 2
    np.fill_diagonal(M, 1.0)
    return M


print("=" * 84)
print("SANITY: the two cases the paper already knows must come out EXACTLY equal")
print("=" * 84)
worst_sanity = 0.0
for n in (3, 4):
    for _ in range(20):
        M = rand_M(n)
        d = rng.uniform(0.1, 3.0, n)
        D = np.diag(d)
        worst_sanity = max(worst_sanity, abs(diameter(D @ M @ D.T) - diameter(M)))
        P = np.eye(n)[rng.permutation(n)]
        worst_sanity = max(worst_sanity, abs(diameter(P @ M @ P.T) - diameter(M)))
        DP = D @ P
        worst_sanity = max(worst_sanity, abs(diameter(DP @ M @ DP.T) - diameter(M)))
print(f"  worst |Delta(SMS^T) - Delta(M)| over diagonal / permutation / monomial S")
print(f"  = {worst_sanity:.3e}   (must be ~0, else the probe is broken)")

print()
print("=" * 84)
print("(MONOTONE): does a genuinely mixing positive S ever INCREASE the diameter?")
print("=" * 84)
print(f"{'n':>3} {'trials':>7} {'max Delta(SMS^T)-Delta(M)':>27} {'any increase?':>15}")
for n in (3, 4, 5):
    worst = -math.inf
    inc = 0
    trials = 300
    for _ in range(trials):
        M = rand_M(n)
        S = rng.uniform(0.05, 1.0, (n, n))
        T = S @ M @ S.T
        if (T <= 0).any():
            continue
        dd = diameter(T) - diameter(M)
        worst = max(worst, dd)
        if dd > 1e-9:
            inc += 1
    print(f"{n:>3} {trials:>7} {worst:>27.3e} {('YES: ' + str(inc)) if inc else 'no':>15}")

print()
print("=" * 84)
print("(STABILISER): near-monomial perturbations -- does equality break at once?")
print("=" * 84)
print(f"{'n':>3} {'perturb':>9} {'Delta(M)':>10} {'Delta(SMS^T)':>13} {'gap':>12}")
for n in (3, 4):
    M = rand_M(n)
    dM = diameter(M)
    d = rng.uniform(0.5, 2.0, n)
    P = np.eye(n)[rng.permutation(n)]
    base = np.diag(d) @ P
    for eps in (0.0, 1e-4, 1e-2, 1e-1):
        S = base + eps * rng.uniform(0.5, 1.0, (n, n))
        T = S @ M @ S.T
        if (T <= 0).any():
            print(f"{n:>3} {eps:>9} {'--- non-positive image, skipped ---':>36}")
            continue
        dT = diameter(T)
        print(f"{n:>3} {eps:>9} {dM:>10.6f} {dT:>13.6f} {dT - dM:>12.3e}")

print()
print("-" * 84)
print("RECONNAISSANCE ONLY.  Decides whether there is a theorem worth a charter.")
