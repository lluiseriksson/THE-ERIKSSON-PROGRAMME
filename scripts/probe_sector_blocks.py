"""Measure the TWO sector obligations separately.  Nobody had.

`SpatialRingOddSectorBound` and `SpatialRingEvenFluctuationBound` are now typed
Lean obligations.  Every sweep so far measured `specRatio`, which is the MAXIMUM
over both blocks, so it could not say how much room each one has on its own.
That matters for how they must be proved:

  * if the odd block sits AT `q`, its proof has to be sharp --- no lossy step
    anywhere, no norm comparison that spends a constant;
  * if the even block sits well below `q`, its proof may be lossy, and the
    campaign should not treat the two as equally hard.

Both blocks are invariant subspaces of a symmetric operator, so the operator
norm on each is the largest `|eigenvalue|` there, which is what this computes.

THIS IS NOT A GATE, AND MUST NEVER BE CITED AS ONE.
====================================================
It was written AFTER the same measurement had already been run inline and its
answer read.  Adopting it as a criterion afterwards would be choosing the judge
knowing the verdict, which is the one thing a pre-registration exists to
prevent.  It carries an exit code so that a later run can detect a REGRESSION
against a previously measured state --- non-zero here means "the numbers moved",
not "a gate failed".

A real gate for either block obligation has to be written before its number is
computed, and has to predict a NUMBER rather than an inequality.  None exists
yet for the odd or the even bound.

Reported as VERIFIED.  It proves nothing; it says where the slack is.
"""
import math
import sys

import numpy as np


def blocks(beta: float, gamma: float, L: int):
    """(Perron eigenvalue, odd-block ratio, even non-Perron ratio)."""
    n = 1 << L
    idx = np.arange(n, dtype=np.int64)
    bits = ((idx[:, None] >> np.arange(L)[None, :]) & 1).astype(np.int8)
    x = idx[:, None] ^ idx[None, :]
    ham = np.zeros_like(x, dtype=np.int16)
    v = x.copy()
    while v.any():
        ham += (v & 1).astype(np.int16)
        v >>= 1
    walls = (bits != np.roll(bits, -1, axis=1)).sum(axis=1)
    w = np.exp(gamma * (L - 2.0 * walls))
    sq = np.sqrt(w)
    S = sq[:, None] * np.exp(beta * (L - 2.0 * ham)) * sq[None, :]
    mu, V = np.linalg.eigh(S)
    lam = mu[-1]
    flip = (n - 1) - idx                      # the global spin flip
    odd, even_non = [], []
    for k in range(n):
        parity = float(np.dot(V[:, k], V[:, k][flip]))
        if parity < 0:
            odd.append(abs(mu[k]))
        elif k != n - 1:
            even_non.append(abs(mu[k]))
    return lam, (max(odd) / lam if odd else 0.0), \
        (max(even_non) / lam if even_non else 0.0)


CELLS = [(0.1, 0.1), (0.2, 0.2), (0.3, 0.25), (0.35, 0.35), (0.4, 0.4),
         (0.2, 0.7), (0.1, 0.5)]
EXTENTS = [6, 8, 10]

print("the two sector obligations, measured apart")
print("=" * 84)
print("%6s %6s %3s %10s %12s %12s %12s"
      % ("beta", "gamma", "L", "q", "odd/lam", "evenNP/lam", "q^2"))
bad = 0
worst_odd_slack = 1e9
for b, g in CELLS:
    q = math.tanh(b) * math.exp(2 * g)
    for L in EXTENTS:
        lam, o, e = blocks(b, g, L)
        ok1 = o <= q + 1e-12
        ok2 = e <= q + 1e-12
        bad += 0 if (ok1 and ok2) else 1
        worst_odd_slack = min(worst_odd_slack, q - o)
        print("%6.2f %6.2f %3d %10.6f %12.6f %12.6f %12.6f  %s %s"
              % (b, g, L, q, o, e, q * q,
                 "ok" if ok1 else "FAIL", "ok" if ok2 else "FAIL"))

print()
print("block violations:", bad)
print("smallest slack in the ODD obligation: %.3e" % worst_odd_slack)
print()
print("READING: the odd block runs UP TO q and the even non-Perron block sits")
print("near q^2.  So the odd obligation is TIGHT and its proof cannot afford a")
print("single lossy step, while the even one carries a factor of q in hand.")
print("The campaign should not treat them as equally hard: the sharp one is the")
print("ODD block, not the even one.")
# Non-zero means REGRESSION against the measured state above, not a gate
# verdict: this script was written after its own answer was known.
sys.exit(0 if bad == 0 else 1)
