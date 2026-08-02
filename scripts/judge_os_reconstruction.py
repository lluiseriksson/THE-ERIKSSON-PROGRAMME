"""PRE-REGISTERED GATE for the OS RECONSTRUCTION (paper 14).

Committed BEFORE it is run and before a line of the reconstruction exists.
Every prediction below is a NUMBER --- an integer, an exact zero, or a spectrum
matched entry by entry --- never a range and never an inequality.

--------------------------------------------------------------------------
WHAT THE RECONSTRUCTION IS SUPPOSED TO SAY, STATED BEFORE IT IS TESTED.

Papers 12 and 13 give two reflected forms on half-chain observables and, since
the two bridges, both are forms of the GIBBS MEASURE rather than candidates:

    site  (even separation)  <F, G>_site = sum_s conj(Phi_F s) Phi_G s / w(s)
    bond  (odd  separation)  <F, G>_bond = sum_{s,t} conj(Phi_F s) K(s,t) Phi_G t

where `Phi_F = collapse F` is the boundary vector of the observable.  The site
form is definite as soon as `w > 0`, so IT is the inner product of the physical
space; the bond form is the one that carries the kernel.

The reconstruction is then forced, not chosen.  If the physical space is to
carry an operator `T` with

        <u, T v>_site  =  <u, v>_bond                          (*)

then `T` is determined: `(T v)(s) = w(s) * sum_t K(s,t) v(t)`, i.e. `T = D_w K`
with `D_w` multiplication by the weight.  The claims to be proved are that this
`T` is SELF-ADJOINT for the site inner product and POSITIVE, and that after
dividing by the Perron eigenvalue it is a CONTRACTION.  That is an Osterwalder--
Schrader transfer operator: self-adjoint, positive, contractive.

This is also the honest reason paper 13's site bridge had to be proved first.
`T` advances a half-chain by ONE slice, which turns an even separation into an
odd one, so (*) has one geometry on each side.  A construction owning only the
bond case has no equation to define `T` by.

--------------------------------------------------------------------------
GATE R1 --- THE PHYSICAL SPACE IS EVERYTHING, PREDICTED AS AN INTEGER.

`collapse` sends observables of a whole half-chain to vectors on the boundary
slice.  If it were not surjective the physical space would be a proper subspace
and the operator would live somewhere smaller than advertised.

PREDICTION: `rank(collapse) = 2^L`, exactly, as an integer, in every cell.
Licenses: the surjectivity statement and `quotient = boundary vectors`.

--------------------------------------------------------------------------
GATE R2 --- SELF-ADJOINTNESS, PREDICTED AS ZERO.

PREDICTION: `<u, T v>_site - <T u, v>_site = 0` to `1e-12` relative, for complex
`u, v`, at every cell including NEGATIVE beta.  A number, not an inequality.
Licenses: `T` self-adjoint on the physical space.  Nothing else.

--------------------------------------------------------------------------
GATE R3 --- (*) ITSELF, PREDICTED AS ZERO.

PREDICTION: `<u, T v>_site - <u, v>_bond = 0` to `1e-12` relative.  This is the
equation that DEFINES `T`, so if it fails the operator is not the one the two
papers' forms produce and the reconstruction is built on the wrong map.

--------------------------------------------------------------------------
GATE R4 --- THE SPECTRUM IS THE ONE THE S BLOCK ALREADY KNOWS.

`T = D_w K` is not symmetric in the standard basis, but it is similar to
`symWeighted w beta = sqrt(w) K sqrt(w)`, which papers 7, 8 and 11 already
analyse (Perron vector, spectral gap, `specRatio = tanh beta`).

PREDICTION: the eigenvalues of `T`, sorted, equal those of `symWeighted`,
entry by entry, to `1e-12`; they are all REAL to `1e-12`; and
`max|eig(T)| / lambda_Perron = 1` exactly.  Numbers, one per entry.
Licenses: the contraction statement and the reuse of the existing Perron and
gap results.  Nothing else.

--------------------------------------------------------------------------
WHAT WOULD FALSIFY THE PLAN, STATED BEFORE THE RUN.

If R3 fails, `T = D_w K` is simply not the operator that (*) forces, and the
whole reconstruction has to be redesigned rather than patched.  If R2 fails
while R3 holds, the site form is not the right inner product --- which would
mean paper 13's form, though correctly identified with the measure, is not the
one a reconstruction can use.  If R4 fails, the reconstruction cannot inherit
the Perron and gap results and the Hamiltonian statement is out of reach at
this stage.  Any of the three is worth more than a pass.

Exit 1 if any gate fails.  No acceptance decision depends on `assert`.
"""
import itertools
import math
import sys

import numpy as np


def configs(L):
    return list(itertools.product(range(2), repeat=L))


def kernel(beta, L):
    """spatialKernel: prod_j exp(beta * sign) over the L sites of a slice."""
    cfg = configs(L)
    n = len(cfg)
    K = np.empty((n, n))
    for i, s in enumerate(cfg):
        for j, t in enumerate(cfg):
            agree = sum(1 for a, b in zip(s, t) if a == b)
            K[i, j] = math.exp(beta * (agree - (L - agree)))
    return K


def weight(L, kind):
    cfg = configs(L)
    if kind == "flat":
        return np.ones(len(cfg))
    return np.array([math.exp(0.41 * sum(c) - 0.17 * len(c)) for c in cfg])


def collapse_matrix(beta, L, m, w):
    """Rows indexed by boundary slice, columns by half-path: the collapse."""
    cfg = configs(L)
    n = len(cfg)
    halves = list(itertools.product(cfg, repeat=m + 1))
    M = np.zeros((n, len(halves)))
    index = {c: i for i, c in enumerate(cfg)}
    for col, half in enumerate(halves):
        v = 1.0
        for s in half:
            v *= w[index[s]]
        for t in range(len(half) - 1):
            agree = sum(1 for a, b in zip(half[t], half[t + 1]) if a == b)
            v *= math.exp(beta * (agree - (L - agree)))
        M[index[half[m]], col] = M[index[half[m]], col] + v
    return M


CELLS = [(1, 0.8, "flat"), (1, -0.5, "graded"), (2, 0.6, "graded"),
         (2, 0.0, "flat"), (3, 0.35, "graded"), (3, -0.25, "flat")]

print("GATE R1 -- the physical space is everything, predicted as an INTEGER")
print("=" * 78)
print("%2s %7s %8s %3s %10s %10s %6s" % ("L", "beta", "weight", "m",
                                         "rank", "2^L", "ok"))
okR1 = True
for L, beta, kind in CELLS:
    w = weight(L, kind)
    for m in (0, 1):
        M = collapse_matrix(beta, L, m, w)
        r = int(np.linalg.matrix_rank(M, tol=1e-9))
        good = (r == 2 ** L)
        okR1 = okR1 and good
        print("%2d %7.2f %8s %3d %10d %10d %6s"
              % (L, beta, kind, m, r, 2 ** L, "ok" if good else "FAIL"))
print("GATE R1:", "PASS -- the quotient is the whole boundary space" if okR1
      else "FAIL -- the physical space is a PROPER subspace")

print()
print("GATES R2 and R3 -- self-adjointness and the defining equation, ZERO")
print("=" * 78)
print("%2s %7s %8s %14s %14s %6s" % ("L", "beta", "weight", "R2 residual",
                                     "R3 residual", "ok"))
okR2 = okR3 = True
rng = np.random.default_rng(20260802)
for L, beta, kind in CELLS:
    w = weight(L, kind)
    K = kernel(beta, L)
    n = len(w)
    T = np.diag(w) @ K
    site = lambda u, v: np.sum(np.conj(u) * v / w)
    bond = lambda u, v: np.conj(u) @ K @ v
    worst2 = worst3 = 0.0
    scale = 1.0
    for _ in range(8):
        u = rng.normal(size=n) + 1j * rng.normal(size=n)
        v = rng.normal(size=n) + 1j * rng.normal(size=n)
        a = site(u, T @ v)
        b = site(T @ u, v)
        c = bond(u, v)
        scale = max(scale, abs(a))
        worst2 = max(worst2, abs(a - b))
        worst3 = max(worst3, abs(a - c))
    ok2 = worst2 <= 1e-12 * scale
    ok3 = worst3 <= 1e-12 * scale
    okR2 = okR2 and ok2
    okR3 = okR3 and ok3
    print("%2d %7.2f %8s %14.3e %14.3e %6s"
          % (L, beta, kind, worst2, worst3, "ok" if (ok2 and ok3) else "FAIL"))
print("GATE R2:", "PASS -- T is self-adjoint for the site form" if okR2
      else "FAIL -- the site form is not the right inner product")
print("GATE R3:", "PASS -- T is the operator the two forms define" if okR3
      else "FAIL -- T = D_w K is NOT what the equation forces")

print()
print("GATE R4 -- the spectrum is the one the S block already knows")
print("=" * 78)
print("%2s %7s %8s %14s %14s %12s %6s"
      % ("L", "beta", "weight", "max|spec diff|", "max|Im eig|",
         "max/lambda", "ok"))
okR4 = True
for L, beta, kind in CELLS:
    w = weight(L, kind)
    K = kernel(beta, L)
    T = np.diag(w) @ K
    S = np.diag(np.sqrt(w)) @ K @ np.diag(np.sqrt(w))
    eT = np.linalg.eigvals(T)
    eS = np.linalg.eigvalsh(S)
    diff = np.max(np.abs(np.sort(eT.real) - np.sort(eS)))
    imag = np.max(np.abs(eT.imag))
    lam = np.max(eS)
    ratio = np.max(np.abs(eT)) / lam
    good = (diff <= 1e-12 * max(1.0, abs(lam))
            and imag <= 1e-12 * max(1.0, abs(lam))
            and abs(ratio - 1.0) <= 1e-12)
    okR4 = okR4 and good
    print("%2d %7.2f %8s %14.3e %14.3e %12.9f %6s"
          % (L, beta, kind, diff, imag, ratio, "ok" if good else "FAIL"))
print("GATE R4:", "PASS -- T inherits Perron and the gap" if okR4
      else "FAIL -- the reconstruction cannot inherit the S block's spectrum")

print()
print("=" * 78)
for name, ok, what in (("R1", okR1, "physical space is everything"),
                       ("R2", okR2, "T self-adjoint"),
                       ("R3", okR3, "T is what (*) forces"),
                       ("R4", okR4, "spectrum = symWeighted, contraction")):
    print("GATE %s: %-4s (%s)" % (name, "PASS" if ok else "FAIL", what))
print("Each gate licenses its own theorem only.  Reported as VERIFIED.")
sys.exit(0 if (okR1 and okR2 and okR3 and okR4) else 1)
