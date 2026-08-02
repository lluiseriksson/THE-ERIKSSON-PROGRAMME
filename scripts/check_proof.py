#!/usr/bin/env python3
"""The one step of the MONOTONE proof I derived by hand and could have got wrong.

Claim: with T = S M S^T and w_{abcd} = S_ia S_kb S_jc S_ld >= 0,

    T_ik T_jl = sum_{abcd} w_{abcd} M_ab M_cd
    T_jk T_il = sum_{abcd} w_{abcd} M_cb M_ad        <-- SAME weights

The second identity is the whole trick: it comes from swapping a <-> c in the
expansion of T_jk T_il, which leaves the S-coefficient invariant and moves the
swap onto M.  If that is right, then the cross-ratio bound
M_ab M_cd <= e^Delta M_cb M_ad applies TERMWISE and Delta(SMS^T) <= Delta(M)
follows with no Hilbert metric, no non-expansiveness lemma and no Birkhoff.

Checked against brute force on random S, M and index quadruples.
"""
import numpy as np

rng = np.random.default_rng(777)
worst1 = worst2 = 0.0
cells = 0
for n in (2, 3, 4, 5):
    for _ in range(60):
        S = rng.uniform(0.0, 1.0, (n, n))          # NONnegative, not just positive
        A = rng.uniform(0.2, 1.0, (n, n))
        M = (A + A.T) / 2
        T = S @ M @ S.T
        for (i, j, k, l) in [tuple(rng.integers(0, n, 4)) for _ in range(6)]:
            w = np.einsum('a,b,c,d->abcd', S[i], S[k], S[j], S[l])
            lhs1 = np.einsum('abcd,ab,cd->', w, M, M)
            lhs2 = np.einsum('abcd,cb,ad->', w, M, M)
            worst1 = max(worst1, abs(lhs1 - T[i, k] * T[j, l]))
            worst2 = max(worst2, abs(lhs2 - T[j, k] * T[i, l]))
            cells += 1

print("=" * 78)
print("Weight-matching identity behind the MONOTONE proof")
print("=" * 78)
print(f"  cells checked                                    : {cells}")
print(f"  max | sum w M_ab M_cd  -  T_ik T_jl |            : {worst1:.3e}")
print(f"  max | sum w M_cb M_ad  -  T_jk T_il |            : {worst2:.3e}")
ok = worst1 < 1e-9 and worst2 < 1e-9
print(f"  -> {'IDENTITY HOLDS, the termwise argument is valid' if ok else 'IDENTITY FAILS'}")

# and the consequence, end to end, including S merely NONnegative
import itertools, math
def diameter(M):
    n = M.shape[0]
    hi = -math.inf
    for i, j, k, l in itertools.product(range(n), repeat=4):
        den = M[j, k] * M[i, l]
        if den <= 0:
            return math.inf
        hi = max(hi, (M[i, k] * M[j, l]) / den)
    return math.log(hi)

print()
print("Consequence, with S only NONnegative (stronger than the charter asked):")
worst = -math.inf
n_ok = 0
for n in (3, 4):
    for _ in range(150):
        S = rng.uniform(0.0, 1.0, (n, n))
        A = rng.uniform(0.2, 1.0, (n, n))
        M = (A + A.T) / 2
        np.fill_diagonal(M, 1.0)
        T = S @ M @ S.T
        if (T <= 0).any():
            continue
        g = diameter(T) - diameter(M)
        worst = max(worst, g)
        n_ok += 1
print(f"  {n_ok} cells with nonnegative S, max Delta(SMS^T)-Delta(M) = {worst:.3e}")
raise SystemExit(0 if ok and worst <= 1e-9 else 1)
