#!/usr/bin/env python3
"""Pre-registered gates for D-4, the Gibbs instantiation
(docs/DOBRUSHIN-D3-CHARTER.md lineage; this rung instantiates the comparison
estimate of D-3 at the measure built from an arbitrary positive weight).

Committed BEFORE any Lean of this rung.  These gates do not replace or weaken
J8--J11; they are strictly additional.  What they license:

  G12  INVARIANCE IS AN IDENTITY, NOT AN ESTIMATE.  The heat-bath kernel built
       from a positive weight w by  p_i(eta, s) = w(eta^{i->s}) / sum_t
       w(eta^{i->t})  leaves the normalised measure mu = w/Z invariant:
       E_mu[E_i F] = E_mu[F].  Checked to 1e-12 on deliberately ASYMMETRIC
       weights (no symmetry to hide behind), exhaustively over all Boolean
       observables and all sites.  A residual above roundoff means the
       involution argument planned for the Lean is WRONG and the rung stops.

  G13  THE SIGMOID IDENTITY.  For an Ising weight with symmetric coupling J
       and zero diagonal, the heat-bath conditional at site i equals
       pPlus(h) = (1 + tanh h)/2 at the local field h = sum_k J_ik sigma_k.
       This is the identity D-4b needs to consume D-2a's envelope; residual
       to 1e-12.

  G14  THE ENVELOPE DOMINATES THE INTRINSIC MATRIX.  The minimal (intrinsic)
       Dobrushin coefficients of the Ising measure, computed by exhaustive
       enumeration, satisfy  c_ik <= tanh|J_ik|  entrywise, and the intrinsic
       row sums on the registered in-window cells are BELOW the envelope row
       sums, which are below one.  This is the measured content of "the
       envelope is a majorant, not the minimum" at the level of the MEASURE.

No `assert` anywhere.  Explicit counter; PASS refused if fewer checks ran than
expected.  Output printed IN FULL (Addendum 577).  Runs on the Colab plane.
"""

import itertools
import math
import sys

FAILURES = []
CHECKS = 0


def check(ok, gate, msg):
    global CHECKS
    CHECKS += 1
    if not ok:
        FAILURES.append(f"{gate}: {msg}")
        print(f"    FAIL  {msg}")
    return ok


def configs(n):
    return list(itertools.product((0, 1), repeat=n))


def upd(eta, i, s):
    e = list(eta); e[i] = s; return tuple(e)


def sigma(s):
    return 2 * s - 1


def heat_bath(w, n):
    """Kernel from the weight: p[i][eta][s]."""
    p = {}
    for i in range(n):
        for eta in configs(n):
            tot = sum(w[upd(eta, i, t)] for t in (0, 1))
            for s in (0, 1):
                p[(i, eta, s)] = w[upd(eta, i, s)] / tot
    return p


def mu_of(w):
    Z = sum(w.values())
    return {c: w[c] / Z for c in w}


# ---------------------------------------------------------------- G12
ASYM = {
    2: [1.0, 2.3, 0.7, 5.1],
    3: [1.0, 1.7, 2.3, 3.1, 4.3, 5.9, 7.1, 9.7],
}


def gate_G12():
    print("G12  E_mu[E_i F] = E_mu[F] for the heat-bath kernel of an asymmetric")
    print("     positive weight; exhaustive over Boolean observables and sites")
    worst = 0.0
    for n in (2, 3):
        cfgs = configs(n)
        w = {c: ASYM[n][t] for t, c in enumerate(cfgs)}
        mu = mu_of(w)
        p = heat_bath(w, n)
        wn = 0.0
        for bits in range(1 << len(cfgs)):
            F = {c: float((bits >> t) & 1) for t, c in enumerate(cfgs)}
            EF = sum(mu[c] * F[c] for c in cfgs)
            for i in range(n):
                lhs = sum(mu[c] * sum(p[(i, c, s)] * F[upd(c, i, s)]
                                      for s in (0, 1)) for c in cfgs)
                wn = max(wn, abs(lhs - EF))
        print(f"    n={n}: {1 << len(cfgs)} observables x {n} sites, "
              f"worst |E_mu[E_i F] - E_mu F| = {wn:.3e}")
        check(wn <= 1e-12, "G12",
              f"n={n}: invariance residual {wn:.3e} above 1e-12 -- the "
              f"involution argument is wrong and D-4a must stop")
        worst = max(worst, wn)
    print(f"    -> worst residual {worst:.3e}")


# ---------------------------------------------------------------- G13/G14
def ising_weight(n, J):
    """w(eta) = exp( (1/2) sum_{j,k} J[j][k] sigma_j sigma_k ), J symmetric,
    zero diagonal."""
    w = {}
    for c in configs(n):
        e = 0.0
        for j in range(n):
            for k in range(n):
                e += J[j][k] * sigma(c[j]) * sigma(c[k])
        w[c] = math.exp(e / 2)
    return w


def chain_J(n, beta):
    J = [[0.0] * n for _ in range(n)]
    for j in range(n - 1):
        J[j][j + 1] = beta
        J[j + 1][j] = beta
    return J


def aniso_J(beta, gamma):
    """Four sites on a 2x2 cell: horizontal beta, vertical gamma."""
    J = [[0.0] * 4 for _ in range(4)]
    for (a, b, v) in ((0, 1, beta), (2, 3, beta), (0, 2, gamma), (1, 3, gamma)):
        J[a][b] = v
        J[b][a] = v
    return J


def gate_G13():
    print("G13  heat-bath conditional == (1 + tanh h)/2 at h = sum_k J_ik sigma_k")
    worst = 0.0
    cells = [(3, chain_J(3, 0.4)), (3, chain_J(3, 0.9)), (4, aniso_J(0.2, 0.1))]
    for n, J in cells:
        w = ising_weight(n, J)
        p = heat_bath(w, n)
        wn = 0.0
        for eta in configs(n):
            for i in range(n):
                h = sum(J[i][k] * sigma(eta[k]) for k in range(n) if k != i)
                wn = max(wn, abs(p[(i, eta, 1)] - (1 + math.tanh(h)) / 2))
        print(f"    n={n}: worst |p_i(+1) - pPlus(h)| = {wn:.3e}")
        check(wn <= 1e-12, "G13",
              f"n={n}: sigmoid identity residual {wn:.3e} -- the local-field "
              f"factorisation planned for D-4b is wrong")
        worst = max(worst, wn)
    print(f"    -> worst residual {worst:.3e}")


def intrinsic_C(w, n):
    p = heat_bath(w, n)
    C = [[0.0] * n for _ in range(n)]
    for i in range(n):
        for k in range(n):
            if i == k:
                continue
            best = 0.0
            for eta in configs(n):
                for s in (0, 1):
                    etap = upd(eta, k, s)
                    tv = 0.5 * sum(abs(p[(i, eta, t)] - p[(i, etap, t)])
                                   for t in (0, 1))
                    best = max(best, tv)
            C[i][k] = best
    return C


def gate_G14():
    print("G14  intrinsic c_ik <= tanh|J_ik| entrywise, and in-window row sums")
    cells = [("chain b=0.2", 3, chain_J(3, 0.2)),
             ("chain b=0.35", 3, chain_J(3, 0.35)),
             ("aniso b=0.2 g=0.1", 4, aniso_J(0.2, 0.1))]
    for name, n, J in cells:
        w = ising_weight(n, J)
        C = intrinsic_C(w, n)
        margin = float("inf")
        viol = 0
        for i in range(n):
            for k in range(n):
                if i == k:
                    continue
                env = math.tanh(abs(J[i][k]))
                if C[i][k] > env + 1e-12:
                    viol += 1
                if J[i][k] != 0.0:
                    margin = min(margin, env - C[i][k])
        rows_c = max(sum(C[i]) for i in range(n))
        rows_e = max(sum(math.tanh(abs(J[i][k])) for k in range(n))
                     for i in range(n))
        print(f"    {name}: violations={viol}, min (tanh|J| - c) on bonds = "
              f"{margin:+.6e}, max row sum intrinsic={rows_c:.6f} "
              f"envelope={rows_e:.6f}")
        check(viol == 0, "G14",
              f"{name}: intrinsic coefficient EXCEEDS the envelope -- D-2a's "
              f"majorant claim fails at the measure and D-4b must stop")
        check(rows_c <= rows_e + 1e-12, "G14",
              f"{name}: intrinsic row sum above envelope row sum")
        check(rows_e < 1.0, "G14",
              f"{name}: registered cell is not in the envelope window")


def main():
    print("=" * 74)
    print("GATES — D-4, THE GIBBS INSTANTIATION")
    print("Strictly additional to J8–J11; nothing here weakens an earlier gate.")
    print("=" * 74)
    gate_G12(); print()
    gate_G13(); print()
    gate_G14(); print()
    expected = 2 + 3 + 9
    print("=" * 74)
    print(f"checks performed: {CHECKS} (expected {expected})")
    if CHECKS < expected:
        print("VERDICT: FAIL — fewer checks ran than expected")
        return 1
    if FAILURES:
        print(f"VERDICT: FAIL ({len(FAILURES)})")
        for f in FAILURES:
            print("  -", f)
        return 1
    print("VERDICT: PASS — invariance is an identity, the sigmoid "
          "factorisation holds, and the envelope dominates the intrinsic "
          "matrix on every registered cell")
    return 0


if __name__ == "__main__":
    sys.exit(main())
