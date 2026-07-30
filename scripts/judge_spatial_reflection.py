"""PRE-REGISTERED JUDGE for the reflection-positivity campaign (paper 12).

Committed BEFORE any Lean is written.

--------------------------------------------------------------------------
TWO GATES, SEPARATE ON PURPOSE.

The previous campaign's judge ended in ONE joint gate over two independent
targets.  Half of it failed, the gate read FAIL, and the work went ahead anyway
-- which is recorded as a process violation in Addendum 548 and cannot be
undone.  The remedy is structural and is applied here: **each prediction
authorises its own theorem and nothing else**, and the gates are written before
any number is looked at.

--------------------------------------------------------------------------
GATE A -- reflection through a SITE (even separation).

Claim: for EVERY beta, including negative, every positive source weight and
every observable,

    gibbsPathSum(w, beta, N, A, A) >= 0     for N EVEN.

Rationale to be proved: the sum is <dress A, K^N dress A> and for even N that is
a square.  If this fails numerically, the factorisation is wrong and no
site-reflection theorem is attempted.
PASS iff no cell goes below -1e-9 (relative to the scale of the sum).

--------------------------------------------------------------------------
GATE B -- reflection through a BOND (odd separation).

Claim, in two halves, BOTH required:

  (B1) for beta >= 0, the same sum is >= 0 for N ODD;
  (B2) for beta < 0 the statement FAILS -- there exists an observable making it
       strictly negative.  A theorem whose hypothesis is never active is not
       worth stating, so the gate demands the failure be exhibited, not merely
       absent.

PASS iff B1 shows no violation and B2 exhibits one in every negative-beta cell.

--------------------------------------------------------------------------
GATE A authorises only the even-separation theorem.
GATE B authorises only the beta >= 0 theorem and its sharpness witness.
Neither authorises the other.  Reported as VERIFIED, never as proved.
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
    """Brute force over paths: sum_X A(X_0) A(X_N) prod w prod K."""
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


def random_weight(L, gamma):
    """A strictly positive, deliberately NON-constant source weight."""
    cfgs = configs(L)
    return {c: math.exp(gamma * rng.normal()) for c in cfgs}


def worst(L, beta, N, gamma, trials):
    """Most negative value of the reflected sum over random observables."""
    cfgs = configs(L)
    w = random_weight(L, gamma)
    lo, scale = 0.0, 1.0
    for _ in range(trials):
        A = {c: float(rng.normal()) for c in cfgs}
        v = gibbs_path_sum(L, beta, w, N, A)
        scale = max(scale, abs(v))
        lo = min(lo, v)
    return lo, scale


print("GATE A -- site reflection (N EVEN), claimed for EVERY beta")
print("=" * 72)
print(f"{'L':>2} {'beta':>7} {'N':>3} {'gamma':>6} {'most negative':>16} {'ok':>5}")
okA = True
for L, N in [(1, 2), (2, 2), (1, 4), (2, 4)]:
    for beta in [0.7, 0.0, -0.4, -1.1]:
        lo, scale = worst(L, beta, N, 0.6, 60)
        good = lo >= -1e-9 * scale
        okA = okA and good
        print(f"{L:>2} {beta:>7.2f} {N:>3} {0.6:>6.2f} {lo:>16.3e} "
              f"{'ok' if good else 'FAIL':>5}")
print("GATE A:", "PASS -- site-reflection theorem authorised" if okA
      else "FAIL -- do not fabricate the site-reflection theorem")

print()
print("GATE B1 -- bond reflection (N ODD) at beta >= 0")
print("=" * 72)
print(f"{'L':>2} {'beta':>7} {'N':>3} {'gamma':>6} {'most negative':>16} {'ok':>5}")
okB1 = True
for L, N in [(1, 1), (2, 1), (1, 3), (2, 3)]:
    for beta in [1.2, 0.5, 0.1, 0.0]:
        lo, scale = worst(L, beta, N, 0.6, 60)
        good = lo >= -1e-9 * scale
        okB1 = okB1 and good
        print(f"{L:>2} {beta:>7.2f} {N:>3} {0.6:>6.2f} {lo:>16.3e} "
              f"{'ok' if good else 'FAIL':>5}")

print()
print("GATE B2 -- and it must FAIL at beta < 0, exhibited not assumed")
print("=" * 72)
print(f"{'L':>2} {'beta':>7} {'N':>3} {'gamma':>6} {'most negative':>16} {'ok':>5}")
okB2 = True
for L, N in [(1, 1), (2, 1), (1, 3), (2, 3)]:
    for beta in [-0.1, -0.5, -1.2]:
        lo, scale = worst(L, beta, N, 0.6, 60)
        good = lo < -1e-9 * scale        # a violation MUST be found
        okB2 = okB2 and good
        print(f"{L:>2} {beta:>7.2f} {N:>3} {0.6:>6.2f} {lo:>16.3e} "
              f"{'ok' if good else 'FAIL':>5}")
print("GATE B:", "PASS -- beta>=0 theorem and its sharpness witness authorised"
      if (okB1 and okB2) else "FAIL -- do not fabricate the bond-reflection theorem")

print()
print("=" * 72)
print("GATE A:", "PASS" if okA else "FAIL", " (site reflection, every beta)")
print("GATE B:", "PASS" if (okB1 and okB2) else "FAIL",
      " (bond reflection, beta >= 0, plus its failure below 0)")
print("Each gate licenses its own theorem only.")
