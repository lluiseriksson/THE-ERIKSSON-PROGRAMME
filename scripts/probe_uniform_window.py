"""PRE-REGISTERED PROBE for the extent-uniformity question.  Committed BEFORE
it is run.

--------------------------------------------------------------------------
WHY THIS EXISTS.

The owner has asked for the extent-uniform bound on the COUPLED kernel, the
lane's long-standing open analytic question, however long it takes.  Before
committing months, the house rule is judges before pages: find out whether the
target is real, and WHERE.

The ring-weighted coupled kernel of this lane,

    K_w(sigma, tau) = sqrt(w(sigma)) * prod_j e^{beta s(sigma_j, tau_j)} * sqrt(w(tau)),
    w(sigma)        = prod_j e^{gamma s(sigma_j, sigma_{j+1})}   (ring),

IS the symmetrised transfer matrix of the anisotropic square-lattice Ising
model, with gamma the horizontal coupling and beta the vertical one.  That is
exact algebra, not an analogy, and it has a consequence: "is there an
extent-uniform spectral bound?" is not an open question of mathematics.  It is
open only as a FORMALISATION, and its answer is known to have a sharp boundary.

--------------------------------------------------------------------------
THE PREDICTION, WRITTEN DOWN BEFORE MEASURING.

Kramers--Wannier duality places the critical line of that model at

    sinh(2 beta) * sinh(2 gamma) = 1.

So the prediction is:

  (P1) for sinh(2b) sinh(2g) < 1  --- the disordered side --- specRatio(L)
       converges to a limit STRICTLY BELOW 1 as L grows, so a uniform bound
       exists;
  (P2) for sinh(2b) sinh(2g) > 1  --- the ordered side --- specRatio(L) tends
       to 1, so NO extent-uniform bound exists and none should be attempted;
  (P3) on the curve itself the ratio drifts towards 1 slowly.

If (P1) and (P2) hold, the honest target is not "uniformity for the coupled
kernel" --- which is FALSE as stated, and the lane has measured it failing ---
but a uniform bound ON AN EXPLICIT WINDOW, with that window's boundary named.
That is a theorem with a shape.  Preregistering it stops a months-long march
towards a statement that is false outside a region nobody wrote down.

--------------------------------------------------------------------------
WHAT WOULD FALSIFY THE PLAN.

If the measured boundary does NOT track sinh(2b)sinh(2g) = 1, then this lane's
kernel is not the model I claim it is, and the entire identification --- which
several papers rest on --- is wrong.  That is the more valuable outcome of the
two, and it is why the run prints the product for every cell rather than a
verdict alone.

PASS iff (P1) holds in every subcritical cell and (P2) in every supercritical
one, with the ratio at L = 12 differing from its L = 8 value by less than 0.02
on the subcritical side (convergence, not coincidence).
Reported as VERIFIED, never as proved.  Exit 1 on failure.
"""
import math
import sys

import numpy as np


def spec_ratio(beta: float, gamma: float, L: int) -> float:
    """|second eigenvalue| / |first|, for the ring-weighted coupled kernel."""
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
    K = sq[:, None] * np.exp(beta * (L - 2.0 * ham)) * sq[None, :]
    mu = np.linalg.eigvalsh(K)
    return float(np.abs(mu[:-1]).max() / mu[-1])


def duality(beta: float, gamma: float) -> float:
    return math.sinh(2 * beta) * math.sinh(2 * gamma)


CELLS = [
    (0.10, 0.10), (0.20, 0.20), (0.15, 0.35), (0.30, 0.25),
    (0.40, 0.40), (0.4407, 0.4407), (0.50, 0.50), (0.60, 0.45),
    (0.80, 0.80), (0.30, 1.20),
]
EXTENTS = [6, 8, 10, 12]

print("specRatio(L) for the ring-weighted coupled kernel")
print("the prediction: bounded away from 1 iff sinh(2b) sinh(2g) < 1")
print("=" * 86)
print("%7s %7s %10s %5s %s" % ("beta", "gamma", "sh*sh", "side",
                               "  ".join("L=%-2d" % L for L in EXTENTS)))

ok = True
rows = []
for beta, gamma in CELLS:
    d = duality(beta, gamma)
    side = "sub" if d < 1 else ("crit" if abs(d - 1) < 1e-3 else "super")
    vals = [spec_ratio(beta, gamma, L) for L in EXTENTS]
    rows.append((beta, gamma, d, side, vals))
    print("%7.4f %7.4f %10.4f %5s %s"
          % (beta, gamma, d, side, "  ".join("%.4f" % v for v in vals)))

print()
print("VERDICTS")
print("=" * 86)
for beta, gamma, d, side, vals in rows:
    last, mid = vals[-1], vals[-2]
    if side == "sub":
        good = last < 0.98 and abs(last - vals[1]) < 0.02
        why = "converged below 1" if good else "NOT bounded away, or still moving"
    elif side == "super":
        good = last > 0.98
        why = "ratio -> 1, no uniform bound" if good else "did NOT approach 1"
    else:
        good = True
        why = "critical cell, reported not judged"
    ok = ok and good
    print("%7.4f %7.4f  %-5s %-8s %s" % (beta, gamma, side,
                                         "ok" if good else "FAIL", why))

print()
print("PROBE:", "PASS -- the window is real and its boundary tracks the duality"
      " curve" if ok else "FAIL -- the identification or the prediction is wrong")
print("This licenses a target of the form: a uniform bound ON THE SUBCRITICAL")
print("WINDOW sinh(2b) sinh(2g) < 1.  It licenses no statement outside it.")
sys.exit(0 if ok else 1)
