"""AUTOPSY of the one cell that failed the pre-registered judge.

Judge 2 predicted, from the Onsager curve, that (beta, gamma) = (0.1, 1.0) --
which has sinh(2b)sinh(2g) = 0.7302 < 1, hence disordered -- would show
specRatio saturating below 1 by L = 12.  It did not: the value at L = 12 is
0.6266, nowhere near 1, but the drift from L = 10 is 3.5e-2, above the
pre-registered 1e-2 threshold, so the cell is UNDECIDED and the judge FAILS.

This file does not re-run the judge with kinder settings.  It prints the whole
sequence for the failing cell so the failure has a diagnosis attached, which is
the only thing the regime allows to be done with it.

The question the sequence answers: is this saturation not yet reached at L = 12,
or a slow crawl towards 1?  The two are distinguished by whether the increments
decay geometrically.
"""
import numpy as np


def specratio(beta, gamma, L):
    n = 1 << L
    idx = np.arange(n, dtype=np.int64)
    x = idx[:, None] ^ idx[None, :]
    ham = np.zeros_like(x, dtype=np.int16)
    v = x.copy()
    while v.any():
        ham += (v & 1).astype(np.int16)
        v >>= 1
    bits = ((idx[:, None] >> np.arange(L)[None, :]) & 1).astype(np.int8)
    walls = (bits != np.roll(bits, -1, axis=1)).sum(axis=1)
    sq = np.sqrt(np.exp(gamma * (L - 2.0 * walls)))
    K = sq[:, None] * np.exp(beta * (L - 2.0 * ham)) * sq[None, :]
    mu = np.linalg.eigvalsh(K)
    return abs(mu[:-1]).max() / mu[-1]


for beta, gamma in [(0.1, 1.0), (0.2, 0.6)]:
    K = np.sinh(2 * beta) * np.sinh(2 * gamma)
    print(f"beta={beta}, gamma={gamma}   sinh(2b)sinh(2g) = {K:.4f}"
          f"  ({'disordered' if K < 1 else 'ordered'})")
    seq = []
    for L in range(1, 13):
        r = specratio(beta, gamma, L)
        seq.append(r)
        inc = "" if L == 1 else f"   d={seq[-1]-seq[-2]:+.6f}"
        print(f"   L={L:<3} {r:.6f}{inc}")
    d = np.diff(seq)
    q = d[-1] / d[-2]
    print(f"   last increment ratio q = {q:.4f}", end="   ")
    if 0 < q < 1:
        print(f"-> geometric extrapolation {seq[-1] + d[-1]*q/(1-q):.4f}")
    else:
        print("-> NOT geometric; no saturation evidence")
    print()

print("VERDICT ON THE JUDGE: unchanged.  It failed, and it stays failed.")
print("The autopsy says only WHICH kind of failure it is; it does not license")
print("the Onsager claim, which is therefore NOT carried into the paper.")
