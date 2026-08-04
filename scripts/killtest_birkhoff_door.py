#!/usr/bin/env python3
"""KILL-TEST for 7-shaped door (1) of ledger Addendum 607: the site-local
projective-cone / beyond-Dobrushin-window contraction mechanism.

REGISTERED TEST (Add. 607, verbatim intent): "30-second kill-test BEFORE
any investment: Birkhoff ratio of sqrt(w) K sqrt(w) at L=2..8 outside the
window; if -> 1 uniformly, dead on arrival."

DEFINITIONS PINNED TO SOURCE (read 2026-08-04 at 06e5ad0ae):
  z2Sign i j  = +1 if i=j else -1          YangMills/OS/Z2Identification.lean:67
  z2Bond b i j = exp(b * z2Sign i j)       YangMills/OS/Z2Identification.lean:76
  z2PathWeight g sigma = prod_t z2Bond g (sigma_t, sigma_{t+1})
                                           YangMills/OS/Z2Identification.lean:84
  sliceW g L  = z2PathWeight g             YangMills/OS/DobrushinCorollary.lean:295
  spatialKernel b sigma tau = prod_j z2Bond b (sigma_j, tau_j)
                                           YangMills/OS/SpatialExtent.lean:84
  symWeighted w b sigma tau = sqrt(w sigma) * spatialKernel b sigma tau
                              * sqrt(w tau) YangMills/OS/PerronGap.lean:322
  window      = 2*tanh|beta| + 2*tanh|gamma| <= 0.8
                                           scripts/judge_os_uniform.py:321
  instantiation (OS-R charter): slice has L+1 sites, w = sliceW gamma L,
  so the matrix acts on {0,1}^(L+1), size 2^(L+1).

BIRKHOFF RATIO: for a strictly positive matrix A, the projective
(Hilbert-metric) diameter of the image cone is
  Delta(A) = max_{j,k} [ max_i log(A_ij/A_ik) + max_i log(A_ik/A_ij) ]
and Birkhoff's theorem gives the contraction coefficient
  kappa(A) = tanh(Delta(A)/4)  in [0,1).
Uniform-in-L contraction in the standard cone requires sup_L kappa < 1.

PRE-REGISTERED DECISION RULE (written before the first run of this file):
the door is DEAD if at EVERY tested outside-window parameter point,
kappa_L is nondecreasing in L (tolerance 1e-12) and 1 - kappa at L=8 is
below 0.01.  It SURVIVES only if some outside-window point shows kappa
bounded away from 1 (1 - kappa_8 >= 0.01) or decreasing.

STRUCTURAL SELF-TESTS of the harness, judged alongside (both are known
theorems; a failure means the harness, not the mathematics, is wrong):
 (a) diagonal-congruence invariance: Delta(sqrt(w) K sqrt(w)) = Delta(K)
     -- multiplying rows and columns by positive diagonals does not move
     the columns projectively, so the site weight w CANNOT change the
     Birkhoff ratio at all;
 (b) tensor additivity (the spatial-birkhoff wall): K is the (L+1)-fold
     tensor power of the 2x2 bond matrix, whose diameter is 4*beta, so
     Delta = 4*beta*(L+1) exactly.

No decision below depends on a Python `assert` (python -O safe): every
check is an explicit comparison feeding an explicit counter.

Local-light contract: single process, matrices at most 512x512 floats
(~2 MB), numpy; wall time printed and required < 30 s by an explicit
check.  Same instrument class as judge_os_uniform.py (measured 0.86 s).
"""

import math
import sys
import time

import numpy as np

passed = 0
failed = 0
failures = []


def check(name, ok):
    global passed, failed
    if ok:
        passed += 1
    else:
        failed += 1
        failures.append(name)
        print(f"  CHECK FAILED: {name}")


def bond_matrix(b):
    return np.array([[math.exp(b), math.exp(-b)],
                     [math.exp(-b), math.exp(b)]], dtype=float)


def log_symweighted(beta, gamma, L):
    """log of symWeighted (sliceW gamma L) beta, on {0,1}^(L+1).

    Returns (logM, logK): with-weight and bare-kernel log matrices."""
    n = L + 1
    size = 1 << n
    # spins as +-1 rows: config index -> site values
    configs = np.array([[1 - 2 * ((s >> j) & 1) for j in range(n)]
                        for s in range(size)], dtype=float)
    # log spatialKernel: beta * sum_j sign(sigma_j, tau_j),
    # sign = sigma_j * tau_j on the +-1 coding
    logK = beta * (configs @ configs.T)
    # log sliceW: gamma * sum_t sigma_t sigma_{t+1}
    logw = gamma * np.sum(configs[:, :-1] * configs[:, 1:], axis=1)
    logM = 0.5 * logw[:, None] + logK + 0.5 * logw[None, :]
    return logM, logK


def hilbert_diameter_from_log(B):
    """Projective diameter of the column family of exp(B), computed in
    log space, full pairwise (no sampling, no caps)."""
    size = B.shape[1]
    best = 0.0
    for j in range(size):
        d = B[:, j:j + 1] - B          # (i, k) -> B_ij - B_ik
        pair = d.max(axis=0) + (-d).max(axis=0)
        m = pair.max()
        if m > best:
            best = float(m)
    return best


def window_value(beta, gamma):
    return 2 * math.tanh(abs(beta)) + 2 * math.tanh(abs(gamma))


def main():
    t0 = time.time()
    params = [
        (0.2, 0.2, True),    # in-window calibration (the charter witness)
        (0.5, 0.3, False),   # outside (judge_os_uniform's own outside case)
        (0.6, 0.6, False),   # outside, deeper
        (1.0, 1.0, False),   # outside, ordered phase
    ]
    Ls = list(range(2, 9))
    tol = 1e-9

    # window membership is checked, not assumed
    for beta, gamma, inside in params:
        wv = window_value(beta, gamma)
        check(f"window membership beta={beta} gamma={gamma}: "
              f"{wv:.4f} {'<=' if inside else '>'} 0.8",
              (wv <= 0.8) == inside)

    kappa = {}
    for beta, gamma, inside in params:
        print(f"parameter point beta={beta} gamma={gamma} "
              f"({'inside' if inside else 'OUTSIDE'} window, "
              f"value {window_value(beta, gamma):.4f})")
        for L in Ls:
            logM, logK = log_symweighted(beta, gamma, L)
            dM = hilbert_diameter_from_log(logM)
            dK = hilbert_diameter_from_log(logK)
            exact = 4.0 * beta * (L + 1)
            k = math.tanh(dM / 4.0)
            kappa[(beta, gamma, L)] = k
            print(f"  L={L}  size={1 << (L + 1):4d}  Delta={dM:.6f}  "
                  f"exact 4b(L+1)={exact:.6f}  kappa={k:.12f}")
            check(f"(a) w-invariance beta={beta} gamma={gamma} L={L}",
                  abs(dM - dK) <= tol * max(1.0, abs(dK)))
            check(f"(b) tensor additivity beta={beta} gamma={gamma} L={L}",
                  abs(dM - exact) <= tol * max(1.0, exact))

    # the registered kill criterion, outside-window points only
    dead_everywhere = True
    for beta, gamma, inside in params:
        ks = [kappa[(beta, gamma, L)] for L in Ls]
        for a, b in zip(ks, ks[1:]):
            check(f"kappa nondecreasing beta={beta} gamma={gamma}",
                  b >= a - 1e-12)
        if not inside:
            tail = 1.0 - ks[-1]
            approaches_one = tail < 0.01
            check(f"kappa -> 1 at L=8 (1-kappa={tail:.3e}) "
                  f"beta={beta} gamma={gamma}", approaches_one)
            if not (approaches_one and
                    all(b >= a - 1e-12 for a, b in zip(ks, ks[1:]))):
                dead_everywhere = False

    wall = time.time() - t0
    print(f"wall time: {wall:.2f} s (local-light limit 30 s)")
    check(f"local-light wall time {wall:.2f}s < 30s", wall < 30.0)

    expected = 4 + 4 * 7 * 2 + 4 * 6 + 3 + 1
    total = passed + failed
    print("=" * 64)
    print(f"checks run: {total}  passed: {passed}  failed: {failed}  "
          f"expected: {expected}")
    if failures:
        print("failures:")
        for f in failures:
            print(f"  - {f}")
    if failed == 0 and total == expected:
        print("HARNESS VERDICT: PASS (all checks, count matches registration)")
        if dead_everywhere:
            print("KILL-TEST VERDICT: DOOR (1) IS DEAD ON ARRIVAL -- the "
                  "Birkhoff ratio of sqrt(w) K sqrt(w) tends to 1 at every "
                  "tested outside-window point (and the site weight w is "
                  "projectively invisible: Delta(sqrt(w) K sqrt(w)) = "
                  "Delta(K) = 4 beta (L+1) exactly).")
        else:
            print("KILL-TEST VERDICT: DOOR (1) SURVIVES the registered "
                  "criterion at some outside-window point; charter it.")
        return 0
    print("HARNESS VERDICT: FAIL -- the kill-test run is NOT usable; "
          "no door verdict is emitted from a failed harness.")
    return 1


if __name__ == "__main__":
    sys.exit(main())
