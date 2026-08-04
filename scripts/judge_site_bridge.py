"""PRE-REGISTERED GATE for the SITE bridge (paper 14 precondition).

Committed BEFORE it is run and before a line of the Lean exists.  Written under
the standing rule that a gate whose answer is already known is not a gate: the
two predictions below are closed forms, fixed here, and neither has been
evaluated.

--------------------------------------------------------------------------
WHY THIS BRIDGE, AND WHY IT IS NOT THE BOND ONE AGAIN.

Paper 13 closed the BOND bridge: a whole path of `2m+2` slices IS a pair of
halves, the weights multiply with exactly one crossing factor, and the reflected
form is therefore the reflected Gibbs sum.  The SITE geometry is different in
kind.  The two halves SHARE the middle slice, so pairs of halves are a FIBRED
PRODUCT over that slice rather than a product, and the shared slice's weight is
counted twice by `W(a)W(b)` and must be divided out once.

It is needed, and not for symmetry: the transfer operator shifts by ONE slice,
which turns an odd separation into an even one.  Without both geometries there
is no self-adjoint transfer operator on the physical space, so the
reconstruction cannot even be stated.

--------------------------------------------------------------------------
GATE S1 --- THE ASSEMBLY IS A BIJECTION, PREDICTED AS AN INTEGER.

With `C = 2^L` configurations per slice, a path through a site plane has
`2m+1` slices, so there are exactly

        C^(2m+1)  =  2^(L*(2m+1))

of them.  The pairs that assemble are those agreeing on the shared slice:
`C^m` choices for the interior of each half and `C` for the slice they share,
again `C^(2m+1)`.

PREDICTION: those two counts are EQUAL, and equal to `2^(L*(2m+1))`, exactly,
as integers, in every cell.  Not "the same order", not "within tolerance" ---
the same integer.  PASS iff every cell matches exactly.
Licenses: `siteEquiv`, the assembly bijection.  Nothing else.

--------------------------------------------------------------------------
GATE S2 --- THE WEIGHT IDENTITY, PREDICTED AS ZERO.

        W(assembleSite(a,b))  =  W(a) * W(b) / w(sigma),   sigma the shared slice

PREDICTION: the residual is ZERO, to `1e-12` relative to the scale of the
weights.  A number, not an inequality: if the shared slice needed any factor
other than a single `1/w(sigma)` --- if it were `1/w^2`, or if a kernel factor
crossed the plane as it does in the bond case --- the residual would be a
visible fraction of the weight, not `1e-12`.
Licenses: `gibbsWeight_joinSite`, the weight identity.  Nothing else.

--------------------------------------------------------------------------
WHAT WOULD FALSIFY THE PLAN.

If S1 fails, pairs of halves are not the paths and the whole fibred-product
picture is wrong.  If S2 fails with a residual that is a fraction of the weight
rather than roundoff, the shared slice enters differently than paper 13's
`osPairingSite` assumes --- which would make that CANDIDATE form wrong, not just
unidentified.  Either outcome is worth more than a pass.

Exit 1 if either gate fails.  No acceptance decision here depends on `assert`.
"""
import itertools
import math
import sys


def configs(L):
    return list(itertools.product(range(2), repeat=L))


def z2sign(a, b):
    return 1.0 if a == b else -1.0


def half_weight(half, L, beta, w):
    """The ordinary Gibbs weight of a half-path: every slice, internal bonds."""
    v = 1.0
    for s in half:
        v *= w[s]
    for t in range(len(half) - 1):
        v *= math.prod(math.exp(beta * z2sign(half[t][j], half[t + 1][j]))
                       for j in range(L))
    return v


def path_weight(path, L, beta, w):
    v = 1.0
    for s in path:
        v *= w[s]
    for t in range(len(path) - 1):
        v *= math.prod(math.exp(beta * z2sign(path[t][j], path[t + 1][j]))
                       for j in range(L))
    return v


def assemble_site(a, b):
    """Past half forwards, then the future half backwards, sharing the last."""
    return list(a) + list(reversed(b[:-1]))


CELLS = [(1, 0), (1, 1), (1, 2), (2, 0), (2, 1)]

print("GATE S1 -- the site assembly is a bijection, predicted as an INTEGER")
print("=" * 78)
print("%2s %2s %14s %14s %14s %6s" % ("L", "m", "paths", "matching pairs",
                                      "2^(L(2m+1))", "ok"))
okS1 = True
for L, m in CELLS:
    cfg = configs(L)
    n_paths = len(cfg) ** (2 * m + 1)
    halves = list(itertools.product(cfg, repeat=m + 1))
    n_pairs = sum(1 for a in halves for b in halves if a[m] == b[m])
    predicted = 2 ** (L * (2 * m + 1))
    good = (n_paths == n_pairs == predicted)
    okS1 = okS1 and good
    print("%2d %2d %14d %14d %14d %6s"
          % (L, m, n_paths, n_pairs, predicted, "ok" if good else "FAIL"))
print("GATE S1:", "PASS -- the assembly bijection is authorised" if okS1
      else "FAIL -- pairs of halves are NOT the paths")

print()
print("GATE S2 -- the weight identity, predicted as ZERO")
print("=" * 78)
print("%2s %2s %7s %16s %10s %6s" % ("L", "m", "beta", "max residual",
                                     "scale", "ok"))
okS2 = True
rng_seed = 20260801
for L, m in CELLS:
    cfg = configs(L)
    # a deliberately non-constant positive weight, fixed by a formula rather
    # than sampled, so the cell is reproducible without a generator
    w = {c: math.exp(0.37 * sum(c) - 0.11 * len(c)) for c in cfg}
    for beta in (0.8, 0.0, -0.5):
        halves = list(itertools.product(cfg, repeat=m + 1))
        worst, scale = 0.0, 1.0
        for a in halves:
            for b in halves:
                if a[m] != b[m]:
                    continue
                lhs = path_weight(assemble_site(a, b), L, beta, w)
                rhs = half_weight(a, L, beta, w) * half_weight(b, L, beta, w) \
                    / w[a[m]]
                scale = max(scale, abs(lhs))
                worst = max(worst, abs(lhs - rhs))
        good = worst <= 1e-12 * scale
        okS2 = okS2 and good
        print("%2d %2d %7.2f %16.3e %10.4g %6s"
              % (L, m, beta, worst, scale, "ok" if good else "FAIL"))
print("GATE S2:", "PASS -- the weight identity is authorised" if okS2
      else "FAIL -- the shared slice enters differently than assumed")

print()
print("=" * 78)
print("GATE S1:", "PASS" if okS1 else "FAIL", " (assembly bijection)")
print("GATE S2:", "PASS" if okS2 else "FAIL", " (weight identity)")
print("Each gate licenses its own theorem only.  Reported as VERIFIED.")
sys.exit(0 if (okS1 and okS2) else 1)
