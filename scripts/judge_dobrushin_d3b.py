#!/usr/bin/env python3
"""D-3 gates, second round: the constant, and the orientation.

Added after an external reading of the first round.  NEITHER gate replaces or
weakens J8/J9/J10 of `scripts/judge_dobrushin_d3.py`; both are strictly
additional, and the earlier gates stand as run.

  J10q  THE CONSTANT.  The first round tested
            |Cov| <= sum_ij delta_i(f) D_ij delta_j(g)
        and found worst ratios 0.2403 and 0.2217 -- suspiciously near 1/4.  A
        single fair Bernoulli site with f = g = 1_{s=1} has Cov = 1/4,
        osc = 1, D = I, so ANY inequality of this shape needs a constant at
        least 1/4, and 1/4 is therefore the natural target:
            |Cov| <= (1/4) * sum_ij delta_i(f) D_ij delta_j(g).
        Formalising the constant-1 version would mechanise a statement four
        times weaker than the one available.  This gate predicts that the
        quarter-constant version HOLDS on the same exhaustive families, and
        that the Bernoulli control ATTAINS ratio exactly one.

  J11   THE ORIENTATION, and this is the one the first round could not see.
        With C_ij = tanh|J_ij| on an Ising cell, C is SYMMETRIC, so C = C^T and
        D = D^T: a transposed index in the key lemma or in the covariance bound
        would pass every gate of the first round and surface only during general
        composition, possibly months later.  This gate builds a three-site cell
        from eight DISTINCT positive weights, computes the minimal
        coefficients c_ij by EXHAUSTIVE ENUMERATION, EVALUATED NUMERICALLY --
        the minimisation is combinatorially exhaustive, the arithmetic is
        float64 and is not exact, verifies C != C^T, and then runs the key
        lemma and the covariance bound in BOTH orientations.  It discriminates
        only if the declared orientation passes and the transposed one fails;
        if both pass, the gate reports that it cannot discriminate rather than
        claiming a result it did not establish.

DECLARED ORIENTATION, fixed here before any Lean:
    C[i][k]  =  the influence of site k on the single-site conditional at i,
                i.e. sup over eta, eta' differing only at k of
                TV( mu_i(.|eta), mu_i(.|eta') ).
    key lemma:  delta_k(E_i f) <= delta_k(f) + C[i][k] * delta_i(f).
    covariance: |Cov(f,g)| <= (1/4) sum_ij delta_i(f) D[i][j] delta_j(g).

No `assert`.  Explicit counter.  Output printed IN FULL.  Runs on Colab.
"""

import sys
import itertools

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


def tv(p, q):
    return 0.5 * sum(abs(p[s] - q[s]) for s in p)


def delta(k, f, n):
    best = 0.0
    for eta in configs(n):
        for s in (0, 1):
            best = max(best, abs(f[eta] - f[upd(eta, k, s)]))
    return best


# --------------------------------------------------------------------------
# a system given by an ARBITRARY positive measure; conditionals are exact
# --------------------------------------------------------------------------

class System:
    def __init__(self, n, weights):
        self.n = n
        self.cfgs = configs(n)
        Z = sum(weights[c] for c in self.cfgs)
        self.mu = {c: weights[c] / Z for c in self.cfgs}

    def cond(self, i, eta):
        tot = sum(self.mu[upd(eta, i, s)] for s in (0, 1))
        return {s: self.mu[upd(eta, i, s)] / tot for s in (0, 1)}

    def C(self):
        """Minimal coefficients, by exhaustive enumeration, evaluated in float64.
        The minimisation is exhaustive; the arithmetic is not exact."""
        n = self.n
        M = [[0.0] * n for _ in range(n)]
        for i in range(n):
            for k in range(n):
                if i == k:
                    continue
                best = 0.0
                for eta in self.cfgs:
                    for s in (0, 1):
                        best = max(best, tv(self.cond(i, eta),
                                            self.cond(i, upd(eta, k, s))))
                M[i][k] = best
        return M

    def E(self, i, f):
        return {eta: sum(self.cond(i, eta)[s] * f[upd(eta, i, s)] for s in (0, 1))
                for eta in self.cfgs}

    def resolvent(self, C):
        n = self.n
        D = [[1.0 if i == j else 0.0 for j in range(n)] for i in range(n)]
        P = [[1.0 if i == j else 0.0 for j in range(n)] for i in range(n)]
        for _ in range(4000):
            P = [[sum(P[i][k] * C[k][j] for k in range(n)) for j in range(n)]
                 for i in range(n)]
            for i in range(n):
                for j in range(n):
                    D[i][j] += P[i][j]
            if max(max(r) for r in P) < 1e-18:
                break
        return D


def transpose(M):
    n = len(M)
    return [[M[j][i] for j in range(n)] for i in range(n)]


def key_lemma_violations(sysm, C):
    """Number of violations of delta_k(E_i f) <= delta_k(f) + C[i][k] delta_i(f),
    exhaustively over all Boolean observables.  Also the worst margin."""
    n = sysm.n
    nv, worst = 0, float("-inf")
    for bits in range(1 << len(sysm.cfgs)):
        f = {c: float((bits >> t) & 1) for t, c in enumerate(sysm.cfgs)}
        for i in range(n):
            Ef = sysm.E(i, f)
            if delta(i, Ef, n) > 1e-12:
                nv += 1
            for k in range(n):
                if k == i:
                    continue
                lhs = delta(k, Ef, n)
                rhs = delta(k, f, n) + C[i][k] * delta(i, f, n)
                worst = max(worst, lhs - rhs)
                if lhs > rhs + 1e-12:
                    nv += 1
    return nv, worst


def cov_worst_ratio(sysm, D, const):
    n = sysm.n
    worst = 0.0
    for bf in range(1 << len(sysm.cfgs)):
        f = {c: float((bf >> t) & 1) for t, c in enumerate(sysm.cfgs)}
        df = [delta(i, f, n) for i in range(n)]
        Ef = sum(sysm.mu[c] * f[c] for c in sysm.cfgs)
        for bg in range(1 << len(sysm.cfgs)):
            g = {c: float((bg >> t) & 1) for t, c in enumerate(sysm.cfgs)}
            dg = [delta(j, g, n) for j in range(n)]
            Eg = sum(sysm.mu[c] * g[c] for c in sysm.cfgs)
            cov = abs(sum(sysm.mu[c] * f[c] * g[c] for c in sysm.cfgs) - Ef * Eg)
            bound = const * sum(df[i] * D[i][j] * dg[j]
                                for i in range(n) for j in range(n))
            if bound > 1e-15:
                worst = max(worst, cov / bound)
            elif cov > 1e-12:
                return float("inf")
    return worst


# --------------------------------------------------------------------------
# the cells
# --------------------------------------------------------------------------

def ising_weights(n, beta):
    return {c: pow(2.718281828459045,
                   beta * sum((2 * c[j] - 1) * (2 * c[j + 1] - 1)
                              for j in range(n - 1)))
            for c in configs(n)}


ASYM_WEIGHTS = [1.0, 1.7, 2.3, 3.1, 4.3, 5.9, 7.1, 9.7]


def asym_system():
    cfgs = configs(3)
    return System(3, {c: ASYM_WEIGHTS[t] for t, c in enumerate(cfgs)})


# --------------------------------------------------------------------------
# J10q --- the quarter constant
# --------------------------------------------------------------------------

def gate_J10q():
    print("J10q  |Cov| <= (1/4) * sum_ij delta_i(f) D_ij delta_j(g)")
    # the control that forces the constant: one fair Bernoulli site
    one = System(1, {c: 1.0 for c in configs(1)})
    C1 = one.C()
    D1 = one.resolvent(C1)
    r1 = cov_worst_ratio(one, D1, 0.25)
    print(f"    control: one fair site, worst ratio = {r1:.12f}  "
          f"(must be exactly 1: this is what forces the constant 1/4)")
    check(abs(r1 - 1.0) <= 1e-12, "J10q",
          f"the Bernoulli control gives {r1:.15f}, not 1; the constant 1/4 is "
          f"then not the natural one and the target must be restated")
    for n, beta in ((3, 0.2), (3, 0.35)):
        s = System(n, ising_weights(n, beta))
        C = s.C()
        D = s.resolvent(C)
        r = cov_worst_ratio(s, D, 0.25)
        print(f"    ising n={n} beta={beta}: worst ratio = {r:.12f}")
        check(r <= 1.0 + 1e-12, "J10q",
              f"ising n={n} beta={beta}: quarter-constant bound VIOLATED at "
              f"ratio {r:.12f}; the constant 1/4 is too strong and the target "
              f"must be restated rather than the gate weakened")


# --------------------------------------------------------------------------
# J11 --- orientation, on a deliberately non-symmetric cell
# --------------------------------------------------------------------------

def gate_J11():
    print("J11   orientation, on a NON-symmetric cell; minimal c_ij by exhaustive")
    print("      enumeration, evaluated numerically (float64, not exact arithmetic)")
    s = asym_system()
    C = s.C()
    Ct = transpose(C)
    asym = max(abs(C[i][j] - C[j][i]) for i in range(3) for j in range(3))
    print("    C (minimal coefficients, exhaustive enumeration, float64):")
    for row in C:
        print("      " + "  ".join(f"{x:.9f}" for x in row))
    print(f"    max |C - C^T| = {asym:.9f}   (must be > 0, else the gate is blind)")
    check(asym > 1e-6, "J11",
          "the cell is symmetric after all; this gate cannot discriminate "
          "orientation and a transposition would survive it")

    nv, worst = key_lemma_violations(s, C)
    nvt, worstt = key_lemma_violations(s, Ct)
    print(f"    key lemma, DECLARED  orientation: violations={nv}, "
          f"worst(lhs-rhs)={worst:+.3e}")
    print(f"    key lemma, TRANSPOSED orientation: violations={nvt}, "
          f"worst(lhs-rhs)={worstt:+.3e}")
    check(nv == 0, "J11",
          f"the DECLARED orientation fails on the non-symmetric cell "
          f"({nv} violations) -- the convention in the charter is wrong")
    if nvt == 0:
        print("    NOTE: the transposed orientation ALSO passes.  This gate "
              "does not discriminate here, and says so rather than claiming "
              "the convention was confirmed.")
    else:
        print(f"    -> discriminating: the transposed orientation FAILS "
              f"({nvt} violations), so the declared convention is the one the "
              f"lemma needs.")

    D = s.resolvent(C)
    Dt = transpose(D)
    r = cov_worst_ratio(s, D, 0.25)
    rt = cov_worst_ratio(s, Dt, 0.25)
    print(f"    covariance (1/4), D   : worst ratio = {r:.12f}")
    print(f"    covariance (1/4), D^T : worst ratio = {rt:.12f}")
    check(r <= 1.0 + 1e-12, "J11",
          f"the quarter bound fails on the non-symmetric cell with the declared "
          f"D at ratio {r:.12f}")


def main():
    print("=" * 74)
    print("GATES — D-3, SECOND ROUND: the constant and the orientation")
    print("Neither gate replaces or weakens J8/J9/J10; both are additional.")
    print("=" * 74)
    gate_J10q(); print()
    gate_J11(); print()
    expected = 3 + 3
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
    print("VERDICT: PASS")
    return 0


if __name__ == "__main__":
    sys.exit(main())
