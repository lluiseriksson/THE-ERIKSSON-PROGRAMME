"""Independent numerical check of the O-2 bridge theorems.

A Lean proof guarantees that the definitions are internally consistent.  It does
NOT guarantee that they model the object the prose claims.  This script recomputes
both sides of the two load-bearing identities by brute force, from the Boltzmann
weights, with no reference to the Lean development.

  (1) gibbsWeight_eq_dressed
        gibbsWeight(X) = sqrt(w(X_0)) * sqrt(w(X_N)) * prod_t symWeighted(X_t, X_{t+1})

  (2) gibbsPathSum_eq_iterate
        sum_X A(X_0) B(X_N) gibbsWeight(X) = <(K^N) (dress A), dress B>

Run:  python scripts/probe_spatial_gibbs.py
"""
import itertools, math, random

random.seed(20260729)


def configs(L):
    return list(itertools.product([0, 1], repeat=L))


def z2sign(a, b):
    return 1.0 if a == b else -1.0


def spatial_kernel(beta, s, t):
    """prod_j exp(beta * sign(s_j, t_j)) -- the decoupled time-bond weight."""
    return math.prod(math.exp(beta * z2sign(s[j], t[j])) for j in range(len(s)))


def check(L, N, beta, weight):
    cfgs = configs(L)
    w = {c: weight(c) for c in cfgs}

    def gibbs_weight(X):
        """Honest 2D Gibbs weight: spatial factor at EVERY slice, time bonds between."""
        return (math.prod(w[X[t]] for t in range(N + 1)) *
                math.prod(spatial_kernel(beta, X[t], X[t + 1]) for t in range(N)))

    def sym(s, t):
        return math.sqrt(w[s]) * spatial_kernel(beta, s, t) * math.sqrt(w[t])

    paths = list(itertools.product(cfgs, repeat=N + 1))

    # ---- (1) the dressing identity, configuration by configuration
    worst1 = 0.0
    for X in paths:
        lhs = gibbs_weight(X)
        rhs = (math.sqrt(w[X[0]]) * math.sqrt(w[X[N]]) *
               math.prod(sym(X[t], X[t + 1]) for t in range(N)))
        worst1 = max(worst1, abs(lhs - rhs) / max(abs(lhs), 1e-300))

    # ---- (2) the bridge: path sum vs iterated kernel
    A = {c: random.uniform(-2, 2) for c in cfgs}
    B = {c: random.uniform(-2, 2) for c in cfgs}
    lhs2 = sum(A[X[0]] * B[X[N]] * gibbs_weight(X) for X in paths)

    dA = {c: math.sqrt(w[c]) * A[c] for c in cfgs}
    dB = {c: math.sqrt(w[c]) * B[c] for c in cfgs}
    vec = dict(dA)
    for _ in range(N):                       # iterate the SYMMETRISED kernel
        vec = {s: sum(sym(s, t) * vec[t] for t in cfgs) for s in cfgs}
    rhs2 = sum(vec[c] * dB[c] for c in cfgs)
    rel2 = abs(lhs2 - rhs2) / max(abs(lhs2), 1e-300)

    # ---- partition function as a special case
    lhsZ = sum(gibbs_weight(X) for X in paths)
    one = {c: 1.0 for c in cfgs}
    d1 = {c: math.sqrt(w[c]) for c in cfgs}
    vec = dict(d1)
    for _ in range(N):
        vec = {s: sum(sym(s, t) * vec[t] for t in cfgs) for s in cfgs}
    rhsZ = sum(vec[c] * d1[c] for c in cfgs)
    relZ = abs(lhsZ - rhsZ) / max(abs(lhsZ), 1e-300)

    return worst1, rel2, relZ


print("O-2 bridge -- independent recomputation from Boltzmann weights")
print("=" * 66)
print(f"{'L':>2} {'N':>2} {'beta':>6}  {'dressing':>12} {'pathSum':>12} {'partition':>12}")

cases = [
    (1, 1, 0.4), (1, 3, 0.8), (2, 1, 0.3), (2, 2, 0.7),
    (2, 3, 1.1), (3, 2, 0.5), (3, 1, 1.3),
]
worst = 0.0
for L, N, beta in cases:
    # a genuinely configuration-dependent, strictly positive source weight
    gamma = 0.9
    def weight(c, gamma=gamma, L=L):
        return math.exp(gamma * sum(z2sign(c[j], c[(j + 1) % L]) for j in range(L)))
    d, p, z = check(L, N, beta, weight)
    worst = max(worst, d, p, z)
    print(f"{L:>2} {N:>2} {beta:>6.2f}  {d:>12.2e} {p:>12.2e} {z:>12.2e}")

print("=" * 66)
print(f"worst relative discrepancy over all cases: {worst:.3e}")
print("VERDICT:", "PASS" if worst < 1e-12 else "FAIL")
