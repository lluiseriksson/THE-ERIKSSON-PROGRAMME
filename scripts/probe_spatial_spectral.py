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

# ---------------------------------------------------------------------------
# (4) THE COMPOSED ENDPOINT, against the definition of the measure
#
# Everything above is about the operator.  The endpoint is about the normalised
# expectation, which also involves the partition function.  Here the Gibbs sums
# are recomputed by BRUTE FORCE over all paths -- no transfer matrix, no
# dressing identity -- and then compared with C * specRatio^N.

def gibbs_direct(L, beta, gamma, N, A):
    """Partition function and two-point sum, straight from the definition."""
    cfgs = configs(L)
    w = {c: math.exp(gamma * sum(z2sign(c[j], c[(j + 1) % L]) for j in range(L)))
         for c in cfgs}
    Z = 0.0
    S = 0.0
    for path in itertools.product(cfgs, repeat=N + 1):
        weight = math.prod(w[x] for x in path)
        for s in range(N):
            weight *= spatial_kernel(beta, path[s], path[s + 1])
        Z += weight
        S += A[path[0]] * A[path[N]] * weight
    return Z, S


def endpoint_check(L, beta, gamma, Nmax):
    cfgs = configs(L)
    n = len(cfgs)
    w = {c: math.exp(gamma * sum(z2sign(c[j], c[(j + 1) % L]) for j in range(L)))
         for c in cfgs}
    K = np.array([[math.sqrt(w[s]) * spatial_kernel(beta, s, t) * math.sqrt(w[t])
                   for t in cfgs] for s in cfgs])
    mu, V = np.linalg.eigh(K)
    lam = mu[-1]
    omega = V[:, -1]
    if omega[0] < 0:
        omega = -omega                      # the Perron vector, positive branch
    gap = max(abs(m) for m in mu[:-1])
    rho = gap / lam

    # the dressed constant observable, and the overlap c the proof needs
    b = np.array([math.sqrt(w[s]) for s in cfgs])
    cc = float(omega @ b)
    u = b - cc * omega
    nu = float(np.linalg.norm(u))

    # a fluctuation observable: dress(A) orthogonal to omega, A = dress^-1
    dA = V[:, -2]                            # an eigenvector, hence orthogonal
    A = {s: float(dA[i]) / math.sqrt(w[s]) for i, s in enumerate(cfgs)}
    dAn = float(np.linalg.norm(dA))

    # the constant and the threshold, exactly as the Lean proof picks them
    C = 2.0 * dAn * dAn / (cc * cc) + 1.0
    N0 = 0
    while rho ** N0 >= cc * cc / (2.0 * (nu * nu + 1.0)):
        N0 += 1

    ok_bridge, ok_denom, ok_end = True, True, True
    worst = 0.0
    for N in range(1, Nmax + 1):
        KN = np.linalg.matrix_power(K, N)
        Zop = float(b @ KN @ b)
        Sop = float(dA @ KN @ dA)
        # the bridge: brute-force path sums equal the matrix elements
        if n ** (N + 1) <= 300000:
            Zd, Sd = gibbs_direct(L, beta, gamma, N, A)
            ok_bridge = ok_bridge and abs(Zd - Zop) <= 1e-8 * abs(Zop) \
                and abs(Sd - Sop) <= 1e-8 * max(1.0, abs(Sop))
        # the denominator bound of section 8
        ok_denom = ok_denom and (cc * cc * lam ** N - gap ** N * nu * nu
                                 <= Zop * (1 + 1e-9))
        # the endpoint itself
        if N >= N0:
            lhs = abs(Sop / Zop)
            rhs = C * rho ** N
            worst = max(worst, lhs / rhs)
            ok_end = ok_end and lhs <= rhs * (1 + 1e-9)
    return rho, cc, N0, C, worst, ok_bridge, ok_denom, ok_end


print()
print("=" * 78)
print("(4) the COMPOSED endpoint: |E[A(X_0)A(X_N)]| <= C * specRatio^N, N >= N0")
print("    Gibbs sums recomputed by brute force over paths where feasible.")
print(f"{'L':>2} {'beta':>5} {'gamma':>6} {'specRatio':>10} {'N0':>3} "
      f"{'C':>10} {'worst lhs/rhs':>14} {'ok':>4}")
allok4 = True
for L, beta, gamma, Nmax in [(1, 0.4, 0.9, 8), (2, 0.3, 0.4, 8),
                             (2, 0.8, 1.2, 8), (3, 0.5, 0.7, 6)]:
    rho, cc, N0, C, worst, okb, okd, oke = endpoint_check(L, beta, gamma, Nmax)
    ok = okb and okd and oke
    allok4 = allok4 and ok
    print(f"{L:>2} {beta:>5.2f} {gamma:>6.2f} {rho:>10.6f} {N0:>3} "
          f"{C:>10.4f} {worst:>14.6f} {'PASS' if ok else 'FAIL':>4}")
print("    bridge = brute-force path sums match the matrix elements;")
print("    denom  = Z_N >= c^2 lam^N - specGap^N ||u||^2;")
print("    end    = the normalised two-point function obeys C * specRatio^N.")
print("VERDICT (4):", "PASS" if allok4 else "FAIL")
