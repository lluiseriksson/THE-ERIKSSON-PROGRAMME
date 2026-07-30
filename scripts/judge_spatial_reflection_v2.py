"""PRE-REGISTERED JUDGE v2 for paper 12 --- the REDESIGN of gate B.

Committed BEFORE it is run.  Read `judge_spatial_reflection.py` and its autopsy
first: gate B of v1 FAILED and STAYS FAILED.  Nothing here reinterprets it.

--------------------------------------------------------------------------
WHAT WAS WRONG WITH v1's GATE B, and why this is a redesign and not a retry.

v1's gate B bundled two different claims about two different regions --

    (B1) reflection positivity holds for beta >= 0 at odd separation,
    (B2) and fails for beta < 0

-- behind `PASS iff B1 and B2`.  That is the SAME design error the previous
campaign was punished for, committed one level down.  B1 passed everywhere; B2
missed one cell; the bundle failed.

The autopsy measured why B2 missed it: at L=1, beta=-0.1, N=3 the negative
direction carries |D|^N / Z^N ~ 1e-3 of the weight, so a uniformly random
observable lands in the violating cone with probability ~2e-2, and sixty draws
miss it about a third of the time.  **The instrument could not see the effect it
was built to look for.**  An existence claim was being tested by sampling.

The redesign does two things and neither of them lowers a bar:

  * the two claims get SEPARATE gates, each licensing its own theorem;
  * B2 stops sampling and predicts a NUMBER.  That is strictly harder than
    "some draw goes negative": if the identity is off by 1e-12 the gate fails,
    and if the number is not negative below beta = 0 the claim is dead.

--------------------------------------------------------------------------
GATE B1 -- reflection positivity at odd separation, for beta >= 0.
  Random observables, random strictly positive NON-constant source weights.
  PASS iff nothing goes below -1e-9 relative to scale.
  Licenses: the beta >= 0 bond-reflection theorem.  Nothing else.

GATE B2 -- the sharpness witness, by exact prediction.
  For L = 1, constant weight and the odd observable A = (+1,-1),

        gibbsPathSum(beta, N, A, A)  =  2 (e^beta - e^-beta)^N   exactly,

  which is < 0 precisely when beta < 0 and N is odd.
  PASS iff every cell matches to 1e-12 AND the sign behaves as stated.
  Licenses: the sharpness witness.  Nothing else.
"""
import itertools
import sys
import math

import numpy as np

rng = np.random.default_rng(20260731)


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


print("GATE B1 -- odd separation, beta >= 0, random observables and weights")
print("=" * 74)
print(f"{'L':>2} {'beta':>7} {'N':>3} {'most negative':>16} {'ok':>5}")
okB1 = True
for L, N in [(1, 1), (2, 1), (1, 3), (2, 3), (3, 1)]:
    for beta in [1.4, 0.6, 0.2, 0.0]:
        cfgs = configs(L)
        w = {c: math.exp(0.6 * rng.normal()) for c in cfgs}
        lo, scale = 0.0, 1.0
        for _ in range(80):
            A = {c: float(rng.normal()) for c in cfgs}
            v = gibbs_path_sum(L, beta, w, N, A)
            scale = max(scale, abs(v))
            lo = min(lo, v)
        good = lo >= -1e-9 * scale
        okB1 = okB1 and good
        print(f"{L:>2} {beta:>7.2f} {N:>3} {lo:>16.3e} {'ok' if good else 'FAIL':>5}")
print("GATE B1:", "PASS -- beta>=0 bond-reflection theorem authorised" if okB1
      else "FAIL -- do not fabricate it")

print()
print("GATE B2 -- the witness, predicted exactly, not sampled")
print("=" * 74)
print(f"{'beta':>7} {'N':>3} {'measured':>17} {'2 (e^b - e^-b)^N':>19} "
      f"{'|diff|':>10} {'sign ok':>8}")
okB2 = True
w1 = {c: 1.0 for c in configs(1)}
Aodd = {(0,): 1.0, (1,): -1.0}
for beta in [1.0, 0.3, 0.0, -0.1, -0.6, -1.5]:
    for N in [1, 3, 5]:
        v = gibbs_path_sum(1, beta, w1, N, Aodd)
        pred = 2 * (math.exp(beta) - math.exp(-beta)) ** N
        diff = abs(v - pred)
        signok = (v < 0) if beta < 0 else (v >= 0)
        good = diff <= 1e-12 * max(1.0, abs(pred)) and signok
        okB2 = okB2 and good
        print(f"{beta:>7.2f} {N:>3} {v:>17.9e} {pred:>19.9e} {diff:>10.1e} "
              f"{'ok' if signok else 'FAIL':>8}")
print("GATE B2:", "PASS -- sharpness witness authorised" if okB2
      else "FAIL -- do not fabricate the witness")

print()
print("=" * 74)
print("GATE B1:", "PASS" if okB1 else "FAIL", "  (beta >= 0 theorem)")
print("GATE B2:", "PASS" if okB2 else "FAIL", "  (sharpness witness)")
print("v1's GATE B remains FAILED and is not superseded; these are new gates")
print("for the two claims it should never have bundled.")

# A gate that only PRINTS its verdict is a report, not a gate.
sys.exit(0 if (okB1 and okB2) else 1)
