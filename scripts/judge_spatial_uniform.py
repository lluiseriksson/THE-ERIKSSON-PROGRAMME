"""PRE-REGISTERED JUDGE for the uniformity campaign (paper 11).

Committed BEFORE any Lean is written, per the standing rule that no target is
worked unless its own judge passed first.  Two predictions, both falsifiable,
both checked here.

--------------------------------------------------------------------------
PREDICTION 1 -- the decoupled rate is exactly tanh(beta), at EVERY extent.

The S-block kernel at constant source weight is `spatialKernel`, a product over
sites of the 2x2 bond matrix.  If the intended theorem is true, then

    specGap / lambda  =  tanh(beta)      for every L,

to machine precision.  FALSIFIED if any cell deviates by more than 1e-10.
This is the statement paper 11 intends to prove; if the numbers disagree the
campaign stops here.

--------------------------------------------------------------------------
PREDICTION 2 -- the coupled boundary is the Onsager curve.

With the ring source weight the same kernel is (claimed) the symmetrised
transfer matrix of the 2D Ising model, vertical coupling beta and horizontal
coupling gamma.  If that identification is right, the extent-uniformity of
specRatio must switch exactly at the Onsager critical curve

    sinh(2 beta) * sinh(2 gamma)  =  1 .

Concretely, on each pre-registered cell we predict

    K < 1  (disordered)  ->  specRatio(L) SATURATES strictly below 1;
    K > 1  (ordered)     ->  specRatio(L) -> 1.

Operationalised, with the thresholds fixed here and not after seeing results:
    saturating := specRatio(12) < 0.99  and  |specRatio(12)-specRatio(10)| < 1e-2
    running to 1 := specRatio(12) > 0.99
FALSIFIED if any cell's verdict disagrees with the sign of K - 1.  Cells within
10 pct of the curve are EXCLUDED in advance, since finite L cannot resolve them.

--------------------------------------------------------------------------
Reported as VERIFIED, never as proved.  No theorem depends on this file.
"""
import numpy as np

MAXL = 12


def kernel(beta, gamma, L, coupled):
    """Symmetrised S-block kernel; `coupled` switches the ring source weight."""
    n = 1 << L
    idx = np.arange(n, dtype=np.int64)
    x = idx[:, None] ^ idx[None, :]
    ham = np.zeros_like(x, dtype=np.int16)
    v = x.copy()
    while v.any():
        ham += (v & 1).astype(np.int16)
        v >>= 1
    T = np.exp(beta * (L - 2.0 * ham))
    if not coupled:
        return T
    bits = ((idx[:, None] >> np.arange(L)[None, :]) & 1).astype(np.int8)
    walls = (bits != np.roll(bits, -1, axis=1)).sum(axis=1)
    sq = np.sqrt(np.exp(gamma * (L - 2.0 * walls)))
    return sq[:, None] * T * sq[None, :]


def specratio(beta, gamma, L, coupled):
    mu = np.linalg.eigvalsh(kernel(beta, gamma, L, coupled))
    return abs(mu[:-1]).max() / mu[-1]


print("JUDGE 1 -- decoupled rate = tanh(beta) at every extent")
print("=" * 70)
print(f"{'beta':>6} {'L':>3} {'measured':>14} {'tanh(beta)':>14} {'|diff|':>12}")
ok1 = True
for beta in [0.2, 0.5, 0.9]:
    for L in range(1, 9):
        r = specratio(beta, 0.0, L, coupled=False)
        t = np.tanh(beta)
        d = abs(r - t)
        ok1 = ok1 and d < 1e-10
        if L in (1, 4, 8):
            print(f"{beta:>6.2f} {L:>3} {r:>14.12f} {t:>14.12f} {d:>12.2e}")
print("JUDGE 1:", "PASS" if ok1 else "FAIL")

print()
print("JUDGE 2 -- the coupled boundary is sinh(2b)sinh(2g) = 1")
print("=" * 70)
CELLS = [(0.2, 0.2), (0.3, 0.4), (0.2, 0.6), (0.1, 1.0),
         (0.5, 0.6), (0.8, 1.2), (0.6, 0.8), (0.9, 0.5)]
print(f"{'beta':>6} {'gamma':>7} {'K=sh.sh':>10} {'predict':>11} "
      f"{'ratio(12)':>11} {'drift':>10} {'verdict':>11} {'ok':>5}")
ok2 = True
for beta, gamma in CELLS:
    K = np.sinh(2 * beta) * np.sinh(2 * gamma)
    if 0.9 < K < 1.1:
        print(f"{beta:>6.2f} {gamma:>7.2f} {K:>10.4f}  EXCLUDED (within 10 pct of the curve)")
        continue
    predict = "saturate" if K < 1 else "-> 1"
    r12 = specratio(beta, gamma, MAXL, coupled=True)
    r10 = specratio(beta, gamma, MAXL - 2, coupled=True)
    drift = abs(r12 - r10)
    if r12 > 0.99:
        verdict = "-> 1"
    elif drift < 1e-2:
        verdict = "saturate"
    else:
        verdict = "undecided"
    good = verdict == predict
    ok2 = ok2 and good
    print(f"{beta:>6.2f} {gamma:>7.2f} {K:>10.4f} {predict:>11} "
          f"{r12:>11.6f} {drift:>10.2e} {verdict:>11} {'ok' if good else 'FAIL':>5}")
print("JUDGE 2:", "PASS" if ok2 else "FAIL")

print()
print("=" * 70)
print("CAMPAIGN GATE:", "PASS -- fabrication authorised" if (ok1 and ok2)
      else "FAIL -- do not fabricate")
