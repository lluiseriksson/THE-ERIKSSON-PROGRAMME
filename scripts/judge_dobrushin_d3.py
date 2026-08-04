#!/usr/bin/env python3
"""Pre-registered gates for D-3 (docs/DOBRUSHIN-D3-CHARTER.md).

Committed BEFORE any Lean of this rung.  J9 is the gate that can kill D-3c by
brute force before a line of it is written, and it is meant to: if the key lemma
is false on a three-site Ising cell it is false, and no proof effort repairs it.

Every gate exits non-zero on failure.  No `assert` anywhere.  PASS only after an
explicit counter.  Audit output prints IN FULL --- no truncation on any check
whose purpose is to establish absence (Addendum 577).

ENVIRONMENT: run on Colab.  No reliable measurement of cost exists on the
desktop, and the owner's rule of 2026-08-01 presumes heavy without one.
"""

import sys
import itertools
import math

FAILURES = []
CHECKS = 0
EXPECTED_CHECKS = 0     # set at the end of main, from what actually ran


def check(ok, gate, msg):
    global CHECKS
    CHECKS += 1
    if not ok:
        FAILURES.append(f"{gate}: {msg}")
        print(f"    FAIL  {msg}")
    return ok


# --------------------------------------------------------------------------
# the finite system:  S = {-1,+1},  sites 0..n-1 on a path,  Ising conditionals
# --------------------------------------------------------------------------

def configs(n):
    return list(itertools.product((-1, 1), repeat=n))


def neighbours(i, n):
    return [j for j in (i - 1, i + 1) if 0 <= j < n]


def cond(i, eta, beta, n):
    """p(s | eta) for site i, depending on eta only OFF i.  Returns dict s->prob."""
    h = beta * sum(eta[j] for j in neighbours(i, n))
    w = {s: math.exp(h * s) for s in (-1, 1)}
    Z = w[-1] + w[1]
    return {s: w[s] / Z for s in (-1, 1)}


def upd(eta, i, s):
    e = list(eta); e[i] = s; return tuple(e)


def tv(p, q):
    return 0.5 * sum(abs(p[s] - q[s]) for s in p)


def dobrushin_C(n, beta):
    """C[i][j] = sup over eta, eta' differing only at j of TV of the conditionals."""
    C = [[0.0] * n for _ in range(n)]
    for i in range(n):
        for j in range(n):
            if i == j:
                continue
            best = 0.0
            for eta in configs(n):
                for s in (-1, 1):
                    etap = upd(eta, j, s)
                    best = max(best, tv(cond(i, eta, beta, n), cond(i, etap, beta, n)))
            C[i][j] = best
    return C


def E(i, f, beta, n):
    """The single-site conditional expectation operator."""
    return {eta: sum(cond(i, eta, beta, n)[s] * f[upd(eta, i, s)] for s in (-1, 1))
            for eta in configs(n)}


def delta(k, f, n):
    """Oscillation of f in the single coordinate k."""
    best = 0.0
    for eta in configs(n):
        for s in (-1, 1):
            best = max(best, abs(f[eta] - f[upd(eta, k, s)]))
    return best


# --------------------------------------------------------------------------
# J8 --- the analytic ingredient, and that it is attained
# --------------------------------------------------------------------------

def gate_J8():
    print("J8  |sum_s (p_s - q_s) g_s| <= TV(p,q) * osc(g), and attained")
    cases = [
        ({0: 0.5, 1: 0.5}, {0: 0.2, 1: 0.8}, {0: 1.0, 1: 0.0}),
        ({0: 0.9, 1: 0.1}, {0: 0.1, 1: 0.9}, {0: 3.0, 1: -1.0}),
        ({0: 1.0, 1: 0.0}, {0: 0.0, 1: 1.0}, {0: 1.0, 1: 0.0}),
    ]
    worst_ratio = 0.0
    attained = False
    for (p, q, g) in cases:
        lhs = abs(sum((p[s] - q[s]) * g[s] for s in p))
        t = tv(p, q)
        osc = max(g.values()) - min(g.values())
        rhs = t * osc
        ratio = lhs / rhs if rhs > 0 else 0.0
        worst_ratio = max(worst_ratio, ratio)
        if abs(ratio - 1.0) <= 1e-12:
            attained = True
        print(f"    TV={t:.6f} osc={osc:.6f} lhs={lhs:.6f} rhs={rhs:.6f} "
              f"ratio={ratio:.12f}")
        check(lhs <= rhs + 1e-12, "J8", f"bound violated, ratio {ratio:.15f}")
    check(attained, "J8", "the bound is never attained on the registered cases; "
                          "the constant would then not be the constant")
    print(f"    -> worst ratio {worst_ratio:.12f} (must be <= 1, and = 1 somewhere)")


# --------------------------------------------------------------------------
# J9 --- D-3c predicted as a number, exhaustively over ALL Boolean observables
# --------------------------------------------------------------------------

def gate_J9():
    print("J9  delta_k(E_i f) <= delta_k(f) + C[i][k] * delta_i(f),  and")
    print("    delta_i(E_i f) = 0.  Exhaustive over ALL Boolean observables.")
    worst_slack = float("-inf")
    for n, beta in ((2, 0.4), (3, 0.3), (3, 0.9)):
        cfgs = configs(n)
        C = dobrushin_C(n, beta)
        nviol = 0
        worst_here = float("-inf")
        for bits in range(1 << len(cfgs)):
            f = {c: float((bits >> t) & 1) for t, c in enumerate(cfgs)}
            for i in range(n):
                Ef = E(i, f, beta, n)
                # the vanishing clause
                if delta(i, Ef, n) > 1e-12:
                    nviol += 1
                for k in range(n):
                    if k == i:
                        continue
                    lhs = delta(k, Ef, n)
                    rhs = delta(k, f, n) + C[i][k] * delta(i, f, n)
                    worst_here = max(worst_here, lhs - rhs)
                    if lhs > rhs + 1e-12:
                        nviol += 1
        worst_slack = max(worst_slack, worst_here)
        print(f"    n={n} beta={beta}: {1 << len(cfgs)} observables, "
              f"violations={nviol}, worst(lhs-rhs)={worst_here:+.3e}")
        check(nviol == 0, "J9",
              f"n={n} beta={beta}: {nviol} violation(s) of the key lemma")
    print(f"    -> worst (lhs - rhs) over everything: {worst_slack:+.6e} "
          f"(a POSITIVE value refutes D-3c)")


# --------------------------------------------------------------------------
# J10 --- the covariance bound the whole chain exists for
# --------------------------------------------------------------------------

def gibbs(n, beta):
    w = {}
    for eta in configs(n):
        e = sum(eta[j] * eta[j + 1] for j in range(n - 1))
        w[eta] = math.exp(beta * e)
    Z = sum(w.values())
    return {c: w[c] / Z for c in w}


def gate_J10():
    print("J10 |Cov_mu(f,g)| <= sum_ij delta_i(f) D_ij delta_j(g),  D = sum_n C^n")
    for n, beta in ((3, 0.2), (3, 0.35)):
        cfgs = configs(n)
        C = dobrushin_C(n, beta)
        alpha = max(sum(C[i]) for i in range(n))
        mu = gibbs(n, beta)
        # D = sum_n C^n, summed to convergence
        D = [[1.0 if i == j else 0.0 for j in range(n)] for i in range(n)]
        P = [[1.0 if i == j else 0.0 for j in range(n)] for i in range(n)]
        for _ in range(2000):
            P = [[sum(P[i][k] * C[k][j] for k in range(n)) for j in range(n)]
                 for i in range(n)]
            for i in range(n):
                for j in range(n):
                    D[i][j] += P[i][j]
            if max(max(r) for r in P) < 1e-18:
                break
        worst = 0.0
        for bf in range(1 << len(cfgs)):
            f = {c: float((bf >> t) & 1) for t, c in enumerate(cfgs)}
            for bg in range(1 << len(cfgs)):
                g = {c: float((bg >> t) & 1) for t, c in enumerate(cfgs)}
                Ef = sum(mu[c] * f[c] for c in cfgs)
                Eg = sum(mu[c] * g[c] for c in cfgs)
                cov = abs(sum(mu[c] * f[c] * g[c] for c in cfgs) - Ef * Eg)
                bound = sum(delta(i, f, n) * D[i][j] * delta(j, g, n)
                            for i in range(n) for j in range(n))
                if bound > 0:
                    worst = max(worst, cov / bound)
                elif cov > 1e-12:
                    worst = float("inf")
        print(f"    n={n} beta={beta}: alpha={alpha:.6f}, "
              f"worst |Cov|/bound = {worst:.9f}")
        check(alpha < 1.0, "J10", f"n={n} beta={beta}: alpha={alpha} not below 1")
        check(worst <= 1.0 + 1e-12, "J10",
              f"n={n} beta={beta}: covariance bound VIOLATED, ratio {worst:.9f} "
              f"-- the comparison estimate as formulated is wrong")


def main():
    global EXPECTED_CHECKS
    print("=" * 74)
    print("GATES — D-3, THE COMPARISON ESTIMATE  (docs/DOBRUSHIN-D3-CHARTER.md)")
    print("=" * 74)
    gate_J8(); print()
    gate_J9(); print()
    gate_J10(); print()
    EXPECTED_CHECKS = 4 + 3 + 4      # J8: 3 bounds + 1 attainment; J9: 3; J10: 2x2
    print("=" * 74)
    print(f"checks performed: {CHECKS} (expected {EXPECTED_CHECKS})")
    if CHECKS < EXPECTED_CHECKS:
        print("VERDICT: FAIL — fewer checks ran than expected")
        return 1
    if FAILURES:
        print(f"VERDICT: FAIL ({len(FAILURES)})")
        for f in FAILURES:
            print("  -", f)
        return 1
    print("VERDICT: PASS — the key lemma survives exhaustive Boolean testing "
          "and the covariance bound holds on the registered cells")
    return 0


if __name__ == "__main__":
    sys.exit(main())
