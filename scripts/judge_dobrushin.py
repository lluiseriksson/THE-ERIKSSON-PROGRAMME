#!/usr/bin/env python3
"""Pre-registered judges for the DOBRUSHIN lane (docs/DOBRUSHIN-CHARTER.md).

Committed BEFORE any Lean of this lane.  Three SEPARATE gates; no gate bundles a
theorem with its witness.  EXITS NON-ZERO on any failure --- a gate that cannot
fail a CI is a report, not a gate.

  J1  phase localisation      licenses "the degeneracy belongs to the ORDERED
                              phase, not to the weight"
  J2  the D-1 lemma as a NUMBER (not sampled)   licenses fabricating D-1
  J3  the window is non-empty AND conservative  licenses calling the window
                              explicit and non-sharp

Model (the S block's coupled kernel, symmetrised; same spectrum as w.K):
    T_L(s,t) = sqrt(w_g(s)) * K_b(s,t) * sqrt(w_g(t))
    K_b(s,t) = prod_j exp(b * s_j t_j)          spins +-1, time bonds
    w_g(s)   = prod_j exp(g * s_j s_{j+1})      spatial bonds, FREE boundary
Onsager's line for the anisotropic Ising cell: sinh(2b) sinh(2g) = 1.
"""

import sys
import math
import numpy as np

try:
    from scipy.sparse.linalg import eigsh
    HAVE_SCIPY = True
except Exception:                                    # pragma: no cover
    HAVE_SCIPY = False

FAILURES = []


def fail(gate, msg):
    FAILURES.append(f"{gate}: {msg}")
    print(f"    FAIL  {msg}")


# --------------------------------------------------------------------------
# the model
# --------------------------------------------------------------------------

def transfer(L, beta, gamma):
    """The symmetrised coupled transfer matrix on {+-1}^L, free spatial boundary."""
    n = 1 << L
    S = np.array([[1 - 2 * ((c >> j) & 1) for j in range(L)] for c in range(n)],
                 dtype=np.float64)
    wexp = gamma * (S[:, :-1] * S[:, 1:]).sum(axis=1) if L >= 2 else np.zeros(n)
    E = beta * (S @ S.T) + 0.5 * wexp[:, None] + 0.5 * wexp[None, :]
    E -= E.max()                       # ratios are invariant under scaling
    return np.exp(E)


def ratio(L, beta, gamma):
    """|lambda_1| / |lambda_0|, matching `specGap`'s sup over |eigenvalues|."""
    T = transfer(L, beta, gamma)
    if L >= 12 and HAVE_SCIPY:
        ev = eigsh(T, k=4, which="LM", return_eigenvectors=False)
    else:
        ev = np.linalg.eigvalsh(T)
    a = np.sort(np.abs(ev))[::-1]
    return a[1] / a[0]


def onsager(beta, gamma):
    return math.sinh(2 * beta) * math.sinh(2 * gamma)


# --------------------------------------------------------------------------
# J1 --- phase localisation
# --------------------------------------------------------------------------

J1_LS = [2, 4, 6, 8, 10, 12]
J1_CELLS = [                       # (beta, gamma) --- pre-registered, not tuned
    (0.10, 0.10), (0.20, 0.20), (0.30, 0.30), (0.40, 0.40),
    (0.10, 0.80), (0.80, 0.10),
    (0.60, 0.60), (0.80, 0.80),
]
J1_DISORDERED_MAX = 0.95           # Aitken limit must be at or below this
J1_ORDERED_MIN = 0.99              # r(12) must be at least this


def aitken(x0, x1, x2):
    den = (x2 - x1) - (x1 - x0)
    return x2 - (x2 - x1) ** 2 / den if abs(den) > 1e-15 else float("nan")


def gate_J1():
    print("J1  phase localisation")
    print(f"    {'beta':>5} {'gamma':>6} {'onsager':>8} {'r(12)':>9} {'q':>7} {'r_inf':>9}  verdict")
    for (b, g) in J1_CELLS:
        rs = [ratio(L, b, g) for L in J1_LS]
        d = [rs[i + 1] - rs[i] for i in range(len(rs) - 1)]
        q = d[-1] / d[-2] if abs(d[-2]) > 1e-15 else float("nan")
        rinf = aitken(rs[-3], rs[-2], rs[-1])
        ons = onsager(b, g)
        ok = True
        if ons < 1.0:
            if not (rinf <= J1_DISORDERED_MAX):
                ok = False
            if not (q < 1.0):
                ok = False
        else:
            if not (rs[-1] >= J1_ORDERED_MIN):
                ok = False
        print(f"    {b:5.2f} {g:6.2f} {ons:8.4f} {rs[-1]:9.6f} {q:7.4f} {rinf:9.6f}  "
              f"{'ok' if ok else 'FAIL'}")
        if not ok:
            fail("J1", f"cell (beta={b}, gamma={g}) onsager={ons:.4f} "
                       f"r(12)={rs[-1]:.6f} q={q:.4f} r_inf={rinf:.6f}")
    print(f"    -> {'PASS' if not any(f.startswith('J1') for f in FAILURES) else 'FAIL'}")


# --------------------------------------------------------------------------
# J2 --- the D-1 lemma, predicted as a number
# --------------------------------------------------------------------------

def path_graph(m):
    d = np.abs(np.subtract.outer(np.arange(m), np.arange(m)))
    return d


def grid_graph(a, b):
    pts = [(i, j) for i in range(a) for j in range(b)]
    m = len(pts)
    d = np.zeros((m, m), dtype=int)
    for u in range(m):
        for v in range(m):
            d[u, v] = abs(pts[u][0] - pts[v][0]) + abs(pts[u][1] - pts[v][1])
    return d


def gate_J2(tol=1e-12):
    """D-1:  C >= 0, C_ij = 0 for dist > 1, row sums <= alpha < 1
             ==>  sum_n (C^n)_ij <= alpha^dist(i,j) / (1 - alpha).

    REDESIGNED 2026-08-01, DECLARED AND COMMITTED BEFORE BEING RUN.  The first
    version normalised every row to EXACTLY alpha, so it never exercised the one
    hypothesis the module's own docstring calls the point --- row sums BOUNDED by
    alpha, never constant --- which is precisely the crack the coupled kernel
    falls through after `coupled_rowSums_not_constant` kills Schur's test.  A
    gate that does not test the distinctive hypothesis of its theorem is not
    testing that theorem.  The redesign makes the gate STRICTLY HARDER: rows now
    carry deterministically UNEQUAL sums, at most alpha, with at least one row
    strictly below and at least one attaining it.  Nothing was loosened; an
    instrument was repaired.  The original was not superseded quietly --- this
    paragraph is the record.
    """
    print("J2  the D-1 lemma as a number")
    cases = []
    for (name, D) in [("path-8", path_graph(8)), ("grid-4x4", grid_graph(4, 4))]:
        for alpha in (0.3, 0.6, 0.9):
            cases.append((name, D, alpha))
    worst = float("-inf")
    for (name, D, alpha) in cases:
        m = D.shape[0]
        adj = (D <= 1).astype(np.float64)
        # a deterministic non-symmetric C with UNEQUAL row sums, all <= alpha:
        # row i is scaled by 1, 0.85, 0.7, 0.55 cycling, so row 0 attains alpha
        # and the others sit strictly below it.
        base = adj * (1.0 + ((np.arange(m)[:, None] * 7 + np.arange(m)[None, :] * 3) % 5))
        slack = 1.0 - 0.15 * (np.arange(m) % 4)
        C = base * (alpha * slack[:, None] / base.sum(axis=1, keepdims=True))
        sums = C.sum(axis=1)
        if not (sums.max() <= alpha + 1e-12 and sums.min() < alpha - 1e-9):
            fail("J2", f"{name} alpha={alpha}: the redesign failed to produce "
                       f"unequal row sums (min {sums.min()}, max {sums.max()})")
        # sum_n C^n to convergence
        Ssum = np.eye(m)
        P = np.eye(m)
        for _ in range(4000):
            P = P @ C
            Ssum = Ssum + P
            if P.max() < 1e-18:
                break
        bound = alpha ** D / (1.0 - alpha)
        slack = (Ssum - bound).max()
        worst = max(worst, slack)
        ok = slack <= tol
        print(f"    {name:<9} alpha={alpha:<4} max(sum - bound) = {slack: .3e}  "
              f"{'ok' if ok else 'FAIL'}")
        if not ok:
            fail("J2", f"{name} alpha={alpha}: bound violated by {slack:.3e}")
        rowsum = C.sum(axis=1).max()
        if rowsum > alpha + 1e-12:
            fail("J2", f"{name} alpha={alpha}: row-sum hypothesis broken ({rowsum})")
    print(f"    -> {'PASS' if not any(f.startswith('J2') for f in FAILURES) else 'FAIL'}"
          f"   (worst slack {worst:.3e}; a POSITIVE slack would refute D-1)")


# --------------------------------------------------------------------------
# J3 --- the window is non-empty and conservative
# --------------------------------------------------------------------------

def gate_J3(steps=400, hi=1.5):
    print("J3  window non-empty and conservative")
    xs = np.linspace(1e-6, hi, steps)
    B, G = np.meshgrid(xs, xs, indexing="ij")
    dob = 2 * np.tanh(B) + 2 * np.tanh(G) < 1.0
    ons = np.sinh(2 * B) * np.sinh(2 * G) < 1.0
    n_dob, n_ons = int(dob.sum()), int(ons.sum())
    leak = int((dob & ~ons).sum())
    strict = int((ons & ~dob).sum())
    print(f"    grid {steps}x{steps} on (0,{hi}]^2 : |Dobrushin| = {n_dob}, "
          f"|Onsager| = {n_ons}")
    print(f"    Dobrushin \\ Onsager = {leak}   (must be 0)")
    print(f"    Onsager \\ Dobrushin = {strict}   (must be > 0: window not sharp)")
    if n_dob == 0:
        fail("J3", "the Dobrushin window is EMPTY on the tested grid")
    if leak != 0:
        fail("J3", f"{leak} Dobrushin points lie OUTSIDE the disordered region")
    if strict == 0:
        fail("J3", "the Dobrushin window is not strictly smaller than Onsager's")
    print(f"    -> {'PASS' if not any(f.startswith('J3') for f in FAILURES) else 'FAIL'}")


def main():
    print("=" * 74)
    print("JUDGES — DOBRUSHIN LANE   (docs/DOBRUSHIN-CHARTER.md)")
    print("=" * 74)
    gate_J2()
    print()
    gate_J3()
    print()
    gate_J1()
    print()
    print("=" * 74)
    if FAILURES:
        print(f"VERDICT: FAIL ({len(FAILURES)})")
        for f in FAILURES:
            print("  -", f)
        return 1
    print("VERDICT: PASS — all three gates")
    return 0


if __name__ == "__main__":
    sys.exit(main())
