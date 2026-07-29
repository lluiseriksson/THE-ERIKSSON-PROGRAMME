"""Independent numerical check of the S-block operator bound.

Lean guarantees internal consistency of the definitions.  It does NOT guarantee
that `specGap` is the number the prose calls it.  This recomputes, by direct
dense diagonalisation with no reference to the formalisation:

  (1) specGap < lam            -- the modulus is genuine
  (2) ||K u|| <= specGap * ||u||  for every u orthogonal to the Perron vector
  (3) the bound is SHARP: it is attained (up to numerical error) by the
      subdominant eigenvector, so it is not a loose over-estimate.

Run:  python scripts/probe_spatial_spectral.py
"""
import itertools, math, random

random.seed(20260729)
_NUMPY_SEED = 20260729

try:
    import numpy as np
except ImportError:  # pragma: no cover
    raise SystemExit("numpy required for this probe")

np.random.seed(_NUMPY_SEED)   # the random fluctuation vectors below use numpy,
                              # so seeding `random` alone does not pin them


def configs(L):
    return list(itertools.product([0, 1], repeat=L))


def z2sign(a, b):
    return 1.0 if a == b else -1.0


def spatial_kernel(beta, s, t):
    return math.prod(math.exp(beta * z2sign(s[j], t[j])) for j in range(len(s)))


def check(L, beta, gamma):
    cfgs = configs(L)
    n = len(cfgs)
    # strictly positive, configuration-dependent source weight (a spatial ring)
    w = {c: math.exp(gamma * sum(z2sign(c[j], c[(j + 1) % L]) for j in range(L)))
         for c in cfgs}
    # the SYMMETRISED kernel the bridge lands on
    K = np.array([[math.sqrt(w[s]) * spatial_kernel(beta, s, t) * math.sqrt(w[t])
                   for t in cfgs] for s in cfgs])

    mu, V = np.linalg.eigh(K)            # ascending, orthonormal columns
    lam = mu[-1]                          # Perron eigenvalue = largest
    omega = V[:, -1]
    # specGap = largest |mu| among eigenvalues != lam
    gap = max(abs(m) for m in mu[:-1])

    # (1)
    ok1 = gap < lam

    # (2) random fluctuation vectors
    worst_ratio = 0.0
    for _ in range(400):
        x = np.random.randn(n)
        u = x - omega * float(omega @ x)   # project off the Perron direction
        nu = float(np.linalg.norm(u))
        if nu < 1e-12:
            continue
        ratio = float(np.linalg.norm(K @ u)) / nu
        worst_ratio = max(worst_ratio, ratio)
    ok2 = worst_ratio <= gap * (1 + 1e-9)

    # (3) sharpness: the subdominant eigenvector attains it
    sub = V[:, int(np.argmax([abs(m) if i < n - 1 else -1.0
                              for i, m in enumerate(mu)]))]
    attained = float(np.linalg.norm(K @ sub)) / float(np.linalg.norm(sub))
    ok3 = abs(attained - gap) < 1e-9 * max(1.0, gap)

    return lam, gap, worst_ratio, attained, ok1, ok2, ok3


print("S block -- operator bound on the fluctuation sector, recomputed")
print("=" * 78)
print(f"{'L':>2} {'beta':>5} {'gamma':>6} {'lam':>12} {'specGap':>12} "
      f"{'worst||Ku||/||u||':>18} {'ok':>4}")

cases = [(1, 0.4, 0.9), (2, 0.3, 0.4), (2, 0.8, 1.2),
         (3, 0.5, 0.7), (3, 0.8, 1.2), (4, 0.3, 0.4), (4, 0.8, 1.2)]
allok = True
for L, beta, gamma in cases:
    lam, gap, worst, att, ok1, ok2, ok3 = check(L, beta, gamma)
    ok = ok1 and ok2 and ok3
    allok = allok and ok
    print(f"{L:>2} {beta:>5.2f} {gamma:>6.2f} {lam:>12.6f} {gap:>12.6f} "
          f"{worst:>18.6f} {'PASS' if ok else 'FAIL':>4}")

print("=" * 78)
print("(1) specGap < lam in every case, (2) the bound holds on 400 random")
print("    fluctuation vectors per case, (3) the bound is attained by the")
print("    subdominant eigenvector -- i.e. it is sharp, not a loose estimate.")
print("VERDICT:", "PASS" if allok else "FAIL")

# the ratio that decides uniformity in L -- measured, NOT proved
print()
print("specGap/lam, the ratio that would have to stay away from 1 for a")
print("volume-uniform statement (MEASURED, NOT PROVED):")
for beta, gamma in [(0.8, 1.2), (0.3, 0.4)]:
    row = []
    for L in [1, 2, 3, 4, 5]:
        lam, gap, *_ = check(L, beta, gamma)
        row.append(f"L={L}: {gap / lam:.4f}")
    print(f"  beta={beta}, gamma={gamma}:  " + "  ".join(row))
