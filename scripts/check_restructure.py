#!/usr/bin/env python3
"""Three claims the review proposes to build the paper on.  Checked, not adopted.

C1  TWO-SIDED:  Delta(A M B) <= Delta(M) for A,B >= 0 (not just B = A^T).
C2  STRICT:     S entrywise POSITIVE and Delta(M) > 0  =>  Delta(SMS^T) < Delta(M).
C3  WITNESS:    for M^{pq} (all ones except (p,q),(q,p) = mu), Phi = mu^-2 and the
                argmax quadruple set is EXACTLY {(q,q,p,p), (p,p,q,q)}.

C3 is the one the stabiliser route depends on, so it is checked exhaustively,
not sampled.
"""
import itertools, math, sys
import numpy as np

rng = np.random.default_rng(31337)
BAD = []


def Phi(M):
    n = M.shape[0]
    best = -math.inf
    for a, b, c, d in itertools.product(range(n), repeat=4):
        den = M[c, b] * M[a, d]
        if den <= 0:
            return math.inf
        best = max(best, (M[a, b] * M[c, d]) / den)
    return best


print("=" * 84)
print("C1  two-sided:  Delta(A M B) <= Delta(M),  A,B >= 0 independent")
print("=" * 84)
worst = -math.inf
cells = 0
for n in (3, 4, 5):
    for _ in range(150):
        A = rng.uniform(0.0, 1.0, (n, n))
        B = rng.uniform(0.0, 1.0, (n, n))
        M = rng.uniform(0.2, 1.0, (n, n))          # NOT symmetric on purpose
        T = A @ M @ B
        if (T <= 0).any():
            continue
        cells += 1
        g = math.log(Phi(T)) - math.log(Phi(M))
        worst = max(worst, g)
print(f"  {cells} cells (M not symmetric), max Delta(AMB)-Delta(M) = {worst:.3e}")
if worst > 1e-9:
    BAD.append("C1 two-sided FAILS")

print()
print("=" * 84)
print("C2  strict contraction for S > 0 when Delta(M) > 0")
print("=" * 84)
worst_strict = 0.0
cells = 0
for n in (3, 4):
    for _ in range(150):
        S = rng.uniform(0.05, 1.0, (n, n))          # strictly positive
        A = rng.uniform(0.2, 1.0, (n, n))
        M = (A + A.T) / 2
        np.fill_diagonal(M, 1.0)
        dM = math.log(Phi(M))
        if dM <= 1e-9:
            continue
        T = S @ M @ S.T
        g = math.log(Phi(T)) - dM
        cells += 1
        worst_strict = max(worst_strict, g)
        if g >= -1e-12:
            BAD.append(f"C2 not strict: gap={g}")
print(f"  {cells} cells, worst (i.e. least negative) gap = {worst_strict:.3e}")
print(f"  strict in every cell: {not any('C2' in b for b in BAD)}")

print()
print("=" * 84)
print("C3  the witness M^{pq}: Phi = mu^-2 and argmax = {(q,q,p,p),(p,p,q,q)}")
print("=" * 84)
print(f"{'n':>3} {'p,q':>6} {'mu':>7} {'Phi':>12} {'mu^-2':>12} {'#argmax':>8} {'set correct':>12}")
for n in (3, 4, 5):
    for (p, q) in [(0, 1), (0, n - 1), (1, 2)]:
        if p == q or q >= n:
            continue
        for mu in (0.2, 0.7):
            M = np.ones((n, n))
            M[p, q] = M[q, p] = mu
            ph = Phi(M)
            arg = set()
            for a, b, c, d in itertools.product(range(n), repeat=4):
                v = (M[a, b] * M[c, d]) / (M[c, b] * M[a, d])
                if abs(v - ph) < 1e-12:
                    arg.add((a, b, c, d))
            expected = {(q, q, p, p), (p, p, q, q)}
            ok = (abs(ph - mu ** -2) < 1e-12) and (arg == expected)
            print(f"{n:>3} {str((p,q)):>6} {mu:>7.2f} {ph:>12.6f} {mu**-2:>12.6f} "
                  f"{len(arg):>8} {str(ok):>12}")
            if not ok:
                BAD.append(f"C3 n={n} pq={(p,q)} mu={mu}: Phi={ph}, argmax={sorted(arg)}")

print()
print("-" * 84)
if BAD:
    print(f"{len(BAD)} CLAIM(S) FAILED")
    for b in BAD[:6]:
        print("   ", b)
    sys.exit(1)
print("all three claims hold as stated")
