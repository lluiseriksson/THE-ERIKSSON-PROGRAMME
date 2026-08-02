#!/usr/bin/env python3
"""
J12 --- THE COMPOSITION-ORDER GATE for D-3d.

Committed BEFORE any Lean of this rung, per docs/DOBRUSHIN-D3-CHARTER.md.

WHY THIS GATE EXISTS.  J9 fixed the orientation of a SINGLE update:
`C i k` is the influence of `k` on the conditional at `i`, and D-3c proved
`deltaAt k (E i f) <= deltaAt k f + C i k * deltaAt i f` with that orientation.
**That says nothing about the order of a COMPOSITION.**  The claim of D-3d is

    delta (E_{i_m} ... E_{i_1} f)  <=  B_{i_m} ... B_{i_1} delta f

with `B_{i_1}` acting FIRST because `E_{i_1}` was applied first.  A `fold` in the
wrong direction produces `B_{i_1} ... B_{i_m}` instead, and every individual
lemma stays green while the composed statement is false.  That is the cheap
error this gate exists to kill before a line of Lean is written.

NO ACCEPTANCE DECISION HERE DEPENDS ON A PYTHON `assert`: every gate is an
explicit check that appends to FAILURES, and the exit code is derived from an
explicit counter.  Runs identically under `python -O`.

PRE-REGISTERED PREDICTIONS, derived by hand before this file was written, on the
two-site cell taken from the D-3c sharpness witness (site 0 copies site 1 with
probability 3/4; site 1 uniform; C_01 = 1/2, all other entries 0):

    B_0 v = (0, v_1 + v_0/2)          B_1 v = (v_0, 0)
    B_1 B_0 v = (0, 0)                B_0 B_1 v = (0, v_0/2)

  P1  the CORRECT order is never violated, over all Boolean observables and all
      ordered pairs of sites:  worst (lhs - rhs) <= 0 within tolerance.
  P2  the correct order is ATTAINED: worst (lhs - rhs) == 0 exactly for some
      observable and some pair.  A bound never attained would not be the bound.
  P3  the REVERSED product is VIOLATED, and the worst violation margin is
      EXACTLY 0.5 --- realised at sequence (i1, i2) = (1, 0) with
      f = 1{eta_0 = 1}: delta_1(E_0 E_1 f) = 1/2 against a reversed bound of 0.
  P4  the gate DISCRIMINATES: at least one violation of the reversed product
      exists.  If P4 fails the gate is worthless and must be reported as such,
      never quietly passed.

KILL CRITERION: if P1 fails, the composition claim of D-3d as stated is FALSE
on a two-site system.  Stop, report, and do not repair by weakening the
statement.
"""

import itertools
import sys

TOL = 1e-12
CHECKS = 0
FAILURES = []


def check(cond, tag, msg):
    global CHECKS
    CHECKS += 1
    if not cond:
        FAILURES.append("%s: %s" % (tag, msg))
    return bool(cond)


# ---------------------------------------------------------------------------
# The registered cell: two sites, two states, maximally asymmetric influence.
# ---------------------------------------------------------------------------

N = 2
CONFIGS = list(itertools.product((0, 1), repeat=N))


def update(eta, i, s):
    e = list(eta)
    e[i] = s
    return tuple(e)


def kernel(i, eta, s):
    """Site 0 copies site 1 with probability 3/4.  Site 1 is uniform."""
    if i == 0:
        return 0.75 if s == eta[1] else 0.25
    return 0.5


# C[i][k] = influence of k on the conditional at i.
CMAT = [[0.0, 0.5],
        [0.0, 0.0]]


def cond_exp(i, f):
    """E_i f."""
    return {eta: sum(kernel(i, eta, s) * f[update(eta, i, s)] for s in (0, 1))
            for eta in CONFIGS}


def delta(f):
    """The oscillation vector: delta_k f for each site k."""
    out = []
    for k in range(N):
        worst = 0.0
        for eta in CONFIGS:
            for s in (0, 1):
                for t in (0, 1):
                    d = abs(f[update(eta, k, s)] - f[update(eta, k, t)])
                    if d > worst:
                        worst = d
        out.append(worst)
    return out


def bupd(i, v):
    """(B_i v)_k = v_k - [k=i] v_i + C[i][k] * v_i."""
    return [v[k] - (v[i] if k == i else 0.0) + CMAT[i][k] * v[i]
            for k in range(N)]


def observables():
    """Every Boolean observable on the configuration space."""
    for bits in range(1 << len(CONFIGS)):
        yield {c: float((bits >> t) & 1) for t, c in enumerate(CONFIGS)}


# ---------------------------------------------------------------------------
# J12
# ---------------------------------------------------------------------------

def gate_J12():
    print("J12  delta(E_{i2} E_{i1} f) <= B_{i2} B_{i1} delta f,  B_{i1} FIRST.")
    print("     Exhaustive over all Boolean observables and all ordered pairs.")

    worst_correct = float("-inf")
    attained_correct = False
    worst_reversed_violation = float("-inf")
    reversed_violations = 0
    witness = None
    nobs = 0

    for f in observables():
        nobs += 1
        df = delta(f)
        for i1 in range(N):
            for i2 in range(N):
                composed = delta(cond_exp(i2, cond_exp(i1, f)))
                correct = bupd(i2, bupd(i1, df))   # B_{i1} first
                wrong = bupd(i1, bupd(i2, df))     # the fold run backwards
                for k in range(N):
                    slack_c = composed[k] - correct[k]
                    if slack_c > worst_correct:
                        worst_correct = slack_c
                    if abs(slack_c) <= TOL:
                        attained_correct = True
                    slack_w = composed[k] - wrong[k]
                    if slack_w > TOL:
                        reversed_violations += 1
                        if slack_w > worst_reversed_violation:
                            worst_reversed_violation = slack_w
                            witness = (i1, i2, k, composed[k], wrong[k])

    print("     observables tested: %d, ordered pairs: %d" % (nobs, N * N))
    print("     CORRECT order  worst (lhs - rhs) = %+.6e" % worst_correct)
    print("     CORRECT order  attained (== 0)   = %s" % attained_correct)
    print("     REVERSED order violations        = %d" % reversed_violations)
    print("     REVERSED order worst margin      = %+.6e" % worst_reversed_violation)
    if witness is not None:
        i1, i2, k, lhs, rhs = witness
        print("     worst reversed witness: i1=%d i2=%d coord=%d  lhs=%.6f rhs=%.6f"
              % (i1, i2, k, lhs, rhs))

    check(worst_correct <= TOL, "J12/P1",
          "the CORRECT order is VIOLATED by %+.6e -- D-3d as stated is false"
          % worst_correct)
    check(attained_correct, "J12/P2",
          "the correct bound is never attained; then it is not the bound")
    check(reversed_violations > 0, "J12/P4",
          "the reversed product is never violated: this gate does NOT "
          "discriminate composition order and is worthless as written")
    check(abs(worst_reversed_violation - 0.5) <= 1e-9, "J12/P3",
          "predicted worst reversed margin 0.5, measured %.9f"
          % worst_reversed_violation)


def main():
    print("=" * 74)
    print("GATE J12 --- COMPOSITION ORDER  (docs/DOBRUSHIN-D3-CHARTER.md, D-3d)")
    print("=" * 74)
    gate_J12()
    expected = 4
    print("=" * 74)
    print("checks performed: %d (expected %d)" % (CHECKS, expected))
    if CHECKS < expected:
        print("VERDICT: FAIL -- fewer checks ran than expected")
        return 1
    if FAILURES:
        print("VERDICT: FAIL (%d)" % len(FAILURES))
        for f in FAILURES:
            print("  -", f)
        return 1
    print("VERDICT: PASS -- the composition order is B_{i_m} ... B_{i_1}, the "
          "bound is attained, and the reversed product is refuted by 0.5")
    return 0


if __name__ == "__main__":
    sys.exit(main())
