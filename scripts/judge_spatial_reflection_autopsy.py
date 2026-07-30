"""AUTOPSY of GATE B, and the design error that produced it.

GATE B failed on one cell: L=1, N=3, beta=-0.1, where 60 random observables
produced no negative value.

--------------------------------------------------------------------------
THE DESIGN ERROR, stated first because it is the point.

The previous campaign's lesson was: do not bundle independent targets behind one
gate.  That lesson was applied at the top level -- GATE A and GATE B are
separate -- and then repeated ONE LEVEL DOWN: GATE B itself bundles

    (B1) the beta >= 0 theorem
    (B2) its sharpness witness

which are different claims about different regions, joined by "PASS iff B1 and
B2".  B1 passed everywhere.  B2 failed one cell.  The bundle failed, so the gate
failed, and by its own text it authorises neither theorem.

GATE B STAYS FAILED.  It is not reinterpreted.

--------------------------------------------------------------------------
WHY THE CELL FAILED: power, not falsity.

For L=1 the transfer matrix has eigenvalues Z = 2cosh(beta) and D = 2sinh(beta),
so the reflected sum along the even direction scales as Z^N and along the odd
direction as D^N.  At beta = -0.1, N = 3:

    Z^3 ~ 8.05      |D|^3 ~ 8.0e-3

so the negative part is ~1e-3 of the positive part, and a random observable must
land almost exactly on the odd direction for the total to go negative.  Sixty
random draws will essentially never do that.  The design searched for an
existence claim by SAMPLING, which is the wrong instrument.

This file measures that ratio rather than asserting it.
"""
import itertools
import math

import numpy as np

rng = np.random.default_rng(20260730)


def configs(L):
    return list(itertools.product([0, 1], repeat=L))


def z2sign(a, b):
    return 1.0 if a == b else -1.0


def gibbs_path_sum(L, beta, w, N, A):
    cfgs = configs(L)
    total = 0.0
    for path in itertools.product(cfgs, repeat=N + 1):
        weight = math.prod(w[x] for x in path)
        for s in range(N):
            weight *= math.prod(
                math.exp(beta * z2sign(path[s][j], path[s + 1][j]))
                for j in range(L))
        total += A[path[0]] * A[path[N]] * weight
    return total


print("Why 60 random draws missed it: the odd direction is tiny")
print("=" * 70)
print(f"{'beta':>7} {'N':>3} {'Z^N':>12} {'|D|^N':>12} {'ratio':>12} "
      f"{'P(random hit)':>15}")
for beta in [-0.1, -0.5, -1.2]:
    for N in [1, 3]:
        Z = 2 * math.cosh(beta)
        D = abs(2 * math.sinh(beta))
        # fraction of random unit vectors in R^2 whose odd component dominates
        # enough that the total goes negative: |a_odd|^2 |D|^N > |a_even|^2 Z^N
        thr = math.sqrt(Z ** N / D ** N)
        frac = 2 * math.atan(1 / thr) / math.pi
        print(f"{beta:>7.2f} {N:>3} {Z**N:>12.4f} {D**N:>12.3e} "
              f"{(D/Z)**N:>12.3e} {frac:>15.3e}")

print()
print("The same cell, searched along the ODD DIRECTION instead of at random:")
print("=" * 70)
for beta in [-0.1, -0.5, -1.2]:
    for N in [1, 3]:
        w = {c: 1.0 for c in configs(1)}
        A = {(0,): 1.0, (1,): -1.0}
        v = gibbs_path_sum(1, beta, w, N, A)
        pred = 2 * (math.exp(beta) - math.exp(-beta)) ** N
        print(f"  beta={beta:>6.2f} N={N}  value={v:>14.6e}  "
              f"predicted 2 D^N={pred:>14.6e}  diff={abs(v-pred):.2e}")

print()
print("VERDICT: GATE B remains FAILED.  The claim it tested is not refuted --")
print("it is untested, because the instrument could not see an effect of")
print("relative size 1e-3 with sixty random draws.  The repair is a REDESIGN")
print("committed before it is run, not a reinterpretation of this one.")
