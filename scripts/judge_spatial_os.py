"""PRE-REGISTERED JUDGE for paper 13 --- the full OS reflection-positivity axiom
for the coupled Z_2 slice (half-chain algebra, reflection map, complex form).

Committed BEFORE a line of the module's Lean is written.

--------------------------------------------------------------------------
WHY FOUR GATES AND NOT THREE.

The plan announced three.  Writing them down showed that the site collapse and
the bond collapse are two different identities licensing two different theorems,
and the house has now been punished twice for putting two claims behind one
verdict (Addenda 548 and 561).  So the count moved to four, before running
anything.  Changing a pre-registration upward, in public, before it is executed,
is allowed; discovering afterwards that one gate was really two is not.

--------------------------------------------------------------------------
THE OBJECTS.

A slice is `sigma : Fin L -> Fin 2`.  The decoupled kernel is

    K(sigma, tau) = prod_j exp(beta * s(sigma_j, tau_j)),   s = +1 if equal else -1,

`w` is a strictly positive source weight on slices, and a path is
`X_0, ..., X_N` with unnormalised weight

    W(X) = prod_{s=0}^{N} w(X_s) * prod_{s=0}^{N-1} K(X_s, X_{s+1}).

THE HALF-CHAIN ALGEBRA.  An observable of the PAST half is a COMPLEX function
`F` of a whole half-path `a = (X_0, ..., X_m)` --- not of one slice, and not
real.  That is the gap between paper 12 and the Osterwalder--Schrader axiom.

THE REFLECTION.  Theta is path reversal.  With `N = 2m+1` (the plane between
slices m and m+1) the reflected future half is `(X_N, X_{N-1}, ..., X_{m+1})`;
with `N = 2m` (the plane through slice m) it is `(X_{2m}, ..., X_m)`, and the
two halves SHARE the middle slice.  The pairing is

    <Theta F, F>  =  sum over full paths of  conj(F(past)) * F(reflected future) * W(X).

THE COLLAPSE.  Summing out the interior of a half sends `F` to a boundary vector

    (Phi F)(sigma) = sum over a with a_m = sigma of  Wpast(a) * F(a),
    Wpast(a) = prod_{s=0}^{m} w(a_s) * prod_{s=0}^{m-1} K(a_s, a_{s+1}).

Note `Wpast` carries the weight of the boundary slice itself.  The claims to be
tested are that the pairing is exactly a quadratic form in `Phi F`:

    N = 2m    (site):  <Theta F, F> = sum_sigma |Phi F(sigma)|^2 / w(sigma)
    N = 2m+1  (bond):  <Theta F, F> = <Phi F, K Phi F>

--------------------------------------------------------------------------
GATE A1 -- the SITE collapse identity, as a matrix identity, to 1e-12.
  The pairing matrix M is built by BRUTE FORCE over every full path, and
  compared entry by entry against C^T diag(1/w) C.  Not a sign, a number.
  Licenses: the site factorisation lemma.  Nothing else.

GATE A2 -- the BOND collapse identity, same standard, against C^T K C.
  Licenses: the bond factorisation lemma.  Nothing else.

GATE B -- positive semidefiniteness for beta >= 0.
  The MINIMUM EIGENVALUE of the brute-force pairing matrix, which is a
  deterministic quantity, not a sample.  The paper-12 autopsy showed that
  testing a statement about a whole form by drawing observables from it can
  miss a direction that carries 1e-3 of the weight; an eigenvalue cannot.
  Licenses: the axiom-form theorem for beta >= 0.  Nothing else.

GATE C -- and the hypothesis is active below zero.
  At beta < 0 and odd separation the minimum eigenvalue must be strictly
  negative; and in the cell (L=1, m=0, w=1) it must equal exp(beta)-exp(-beta)
  to 1e-12 --- a predicted number, not "some direction goes negative".
  Licenses: the sharpness witness.  Nothing else.

Each gate licenses its own theorem and no other.  Reported as VERIFIED, never
as proved.  Exit code 1 if any gate fails.
"""
import itertools
import math
import sys

import numpy as np


def configs(L):
    return list(itertools.product(range(2), repeat=L))


def kernel_matrix(L, beta):
    """K(sigma, tau) as a dense matrix over the 2^L slices."""
    cfg = configs(L)
    n = len(cfg)
    K = np.empty((n, n))
    for i, s in enumerate(cfg):
        for j, t in enumerate(cfg):
            K[i, j] = math.exp(beta * sum(1 if a == b else -1
                                          for a, b in zip(s, t)))
    return K


def half_paths(n_cfg, m):
    """Every past half-path (X_0, ..., X_m) as a tuple of slice indices."""
    return list(itertools.product(range(n_cfg), repeat=m + 1))


def wpast(a, w, K):
    """prod w over the half, times the internal kernel factors."""
    v = 1.0
    for s in a:
        v *= w[s]
    for s in range(len(a) - 1):
        v *= K[a[s], a[s + 1]]
    return v


def pairing_matrix_bruteforce(L, m, beta, w, odd):
    """M[a, b] = sum over FULL paths whose past half is a and whose reflected
    future half is b, of the full path weight.  Built by enumerating every
    path, so it does not presuppose the factorisation being tested."""
    K = kernel_matrix(L, beta)
    n = K.shape[0]
    N = 2 * m + 1 if odd else 2 * m
    halves = half_paths(n, m)
    index = {a: i for i, a in enumerate(halves)}
    M = np.zeros((len(halves), len(halves)))
    for X in itertools.product(range(n), repeat=N + 1):
        weight = 1.0
        for s in X:
            weight *= w[s]
        for s in range(N):
            weight *= K[X[s], X[s + 1]]
        a = X[:m + 1]
        b = tuple(reversed(X[m + 1:])) if odd else tuple(reversed(X[m:]))
        M[index[a], index[b]] += weight
    return M, K, halves


def collapse_matrix(L, m, w, K, halves):
    """C[sigma, a] = Wpast(a) if a ends at sigma, else 0."""
    n = K.shape[0]
    C = np.zeros((n, len(halves)))
    for j, a in enumerate(halves):
        C[a[m], j] = wpast(a, w, K)
    return C


def random_weight(rng, n, gamma=0.6):
    return np.exp(gamma * rng.normal(size=n))


CELLS = [(1, 0), (1, 1), (1, 2), (2, 0), (2, 1)]
BETAS_NONNEG = [1.1, 0.5, 0.15, 0.0]
BETAS_NEG = [-0.1, -0.5, -1.3]

rng = np.random.default_rng(20260731)
ok = {"A1": True, "A2": True, "B": True, "C": True}

for odd, tag in [(False, "A1"), (True, "A2")]:
    what = "BOND (N = 2m+1)" if odd else "SITE (N = 2m)"
    print("GATE %s -- the %s collapse identity, as a matrix identity" % (tag, what))
    print("=" * 76)
    print("%2s %2s %7s %14s %12s %6s" % ("L", "m", "beta", "max |M - pred|",
                                         "scale", "ok"))
    for (L, m) in CELLS:
        for beta in [0.8, 0.0, -0.7]:
            n = 2 ** L
            w = random_weight(rng, n)
            M, K, halves = pairing_matrix_bruteforce(L, m, beta, w, odd)
            C = collapse_matrix(L, m, w, K, halves)
            pred = C.T @ (K if odd else np.diag(1.0 / w)) @ C
            scale = max(1.0, np.abs(M).max())
            err = np.abs(M - pred).max()
            good = err <= 1e-12 * scale
            ok[tag] = ok[tag] and good
            print("%2d %2d %7.2f %14.3e %12.4g %6s"
                  % (L, m, beta, err, scale, "ok" if good else "FAIL"))
    print("GATE %s:" % tag,
          "PASS -- the %s factorisation lemma is authorised" % what.split()[0].lower()
          if ok[tag] else "FAIL -- do not fabricate it")
    print()

print("GATE B -- positive semidefiniteness at beta >= 0, by MINIMUM EIGENVALUE")
print("=" * 76)
print("%2s %2s %5s %7s %16s %6s" % ("L", "m", "par", "beta", "min eigenvalue",
                                    "ok"))
for (L, m) in CELLS:
    for odd in (False, True):
        for beta in BETAS_NONNEG:
            n = 2 ** L
            w = random_weight(rng, n)
            M, _, _ = pairing_matrix_bruteforce(L, m, beta, w, odd)
            lo = float(np.linalg.eigvalsh((M + M.T) / 2).min())
            scale = max(1.0, np.abs(M).max())
            good = lo >= -1e-9 * scale
            ok["B"] = ok["B"] and good
            print("%2d %2d %5s %7.2f %16.3e %6s"
                  % (L, m, "bond" if odd else "site", beta, lo,
                     "ok" if good else "FAIL"))
print("GATE B:", "PASS -- the beta >= 0 axiom-form theorem is authorised"
      if ok["B"] else "FAIL -- do not fabricate it")
print()

print("GATE C -- and it must FAIL below zero at odd separation, by eigenvalue")
print("=" * 76)
print("%2s %2s %7s %16s %6s" % ("L", "m", "beta", "min eigenvalue", "ok"))
for (L, m) in CELLS:
    for beta in BETAS_NEG:
        n = 2 ** L
        w = random_weight(rng, n)
        M, _, _ = pairing_matrix_bruteforce(L, m, beta, w, True)
        lo = float(np.linalg.eigvalsh((M + M.T) / 2).min())
        scale = max(1.0, np.abs(M).max())
        good = lo < -1e-9 * scale
        ok["C"] = ok["C"] and good
        print("%2d %2d %7.2f %16.3e %6s" % (L, m, beta, lo,
                                            "ok" if good else "FAIL"))

print()
print("and the closed form in the cell (L=1, m=0, w=1): min eig = e^b - e^-b")
print("%7s %18s %18s %10s %6s" % ("beta", "measured", "predicted", "|diff|", "ok"))
for beta in BETAS_NEG + [0.0, 0.4]:
    w = np.ones(2)
    M, _, _ = pairing_matrix_bruteforce(1, 0, beta, w, True)
    lo = float(np.linalg.eigvalsh((M + M.T) / 2).min())
    pred = math.exp(beta) - math.exp(-beta)
    diff = abs(lo - pred)
    good = diff <= 1e-12 * max(1.0, abs(pred))
    ok["C"] = ok["C"] and good
    print("%7.2f %18.10e %18.10e %10.1e %6s"
          % (beta, lo, pred, diff, "ok" if good else "FAIL"))
print("GATE C:", "PASS -- the sharpness witness is authorised"
      if ok["C"] else "FAIL -- do not fabricate it")

print()
print("=" * 76)
for tag, what in [("A1", "site factorisation"), ("A2", "bond factorisation"),
                  ("B", "beta >= 0 axiom form"), ("C", "sharpness witness")]:
    print("GATE %-2s: %-4s  (%s)" % (tag, "PASS" if ok[tag] else "FAIL", what))
print("Each gate licenses its own theorem only.")

# A gate that only PRINTS its verdict is a report, not a gate.
sys.exit(0 if all(ok.values()) else 1)
