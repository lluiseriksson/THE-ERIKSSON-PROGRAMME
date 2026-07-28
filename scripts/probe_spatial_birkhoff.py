"""DESIGN PROBE (not a certificate): what does the Hilbert/Birkhoff route give
for the coupled kernel of the spatial-extent paper?

Kernel:  K(s,t)      = prod_j kb(s_j,t_j),  kb(a,b) = e^{+b} if a==b else e^{-b}
         w_g(s)      = exp(g * sum_j s_j s_{j+1})      (source-only, open chain)
         K_g(s,t)    = w_g(s) * K(s,t)

Claims probed:
 (1) projective cross-ratio of K_g == that of K   (w cancels: source-only)
 (2) projective diameter Delta(K) == 4*beta*L
 (3) Birkhoff contraction coeff tanh(Delta/4) == tanh(beta*L) -> 1 as L grows
 (4) true |lam2/lam1| for the DECOUPLED kernel == |tanh beta|, L-independent
 (5) true |lam2/lam1| for the COUPLED kernel: does it degenerate with L?
"""
import itertools, math
import numpy as np


def configs(L):
    return list(itertools.product([1, -1], repeat=L))


def kernels(beta, gamma, L):
    cs = configs(L)
    n = len(cs)
    K = np.zeros((n, n))
    for i, s in enumerate(cs):
        for j, t in enumerate(cs):
            K[i, j] = math.exp(beta * sum(1 if a == b else -1 for a, b in zip(s, t)))
    w = np.array([math.exp(gamma * sum(s[k] * s[k + 1] for k in range(L - 1))) for s in cs])
    Kg = np.diag(w) @ K
    return K, Kg


def diameter(A):
    n = A.shape[0]
    best = 0.0
    for i in range(n):
        for j in range(n):
            for k in range(n):
                for l in range(n):
                    r = (A[i, k] * A[j, l]) / (A[i, l] * A[j, k])
                    best = max(best, math.log(r))
    return best


def ratio(A):
    ev = np.sort(np.abs(np.linalg.eigvals(A)))[::-1]
    return ev[1] / ev[0]


print(f"{'beta':>5} {'gamma':>6} {'L':>2} | {'Delta(K)':>9} {'Delta(Kg)':>9} {'4*b*L':>8} "
      f"| {'tanh(bL)':>9} | {'|l2/l1| dec':>11} {'tanh b':>8} | {'|l2/l1| coup':>12}")
for beta in (0.3, 0.8):
    for gamma in (0.0, 0.4, 1.2):
        for L in (2, 3, 4):
            K, Kg = kernels(beta, gamma, L)
            dK, dKg = diameter(K), diameter(Kg)
            print(f"{beta:5.2f} {gamma:6.2f} {L:2d} | {dK:9.4f} {dKg:9.4f} {4*beta*L:8.4f} "
                  f"| {math.tanh(beta*L):9.6f} | {ratio(K):11.6f} {math.tanh(beta):8.6f} "
                  f"| {ratio(Kg):12.6f}")
