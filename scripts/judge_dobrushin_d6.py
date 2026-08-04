#!/usr/bin/env python3
"""D-6 gates, registered WITH the charter, BEFORE any Lean of the spectral
rung.  See docs/DOBRUSHIN-D6-CHARTER.md.

  G18  STRIP IDENTITY, exactly: <v, T^n v> by dense linear algebra equals
       the free-boundary strip Gibbs sum with half-dressed v-weighted ends,
       by full enumeration.
  G19  THE TARGET'S NUMERIC SHADOW: specRatio of the normalised coupled
       kernel sits UNDER the Dobrushin window on in-window cells, L = 2..8.
       One out-of-window cell is reported without a pass condition.
  G20  PREFACTOR CONVERGENCE AT FIXED L: the Z-ratio converges to its limit
       geometrically at rate specRatio(L), constant fitted at n=1 only.

No assert; explicit counter; verdict refused if fewer checks ran.
Colab plane; numpy for eigendecomposition (dense, exact convention printed).
"""

import math
import sys
from itertools import product

import numpy as np

CHECKS = 0
FAILURES = []


def check(ok, gate, msg):
    global CHECKS
    CHECKS += 1
    tag = "ok " if ok else "FAIL"
    print(f"  [{tag}] {gate}: {msg}")
    if not ok:
        FAILURES.append(f"{gate}: {msg}")


IN_CELLS = [(0.10, 0.10), (0.12, 0.08), (0.05, 0.15)]
CONTROL_CELL = (0.60, 0.60)


def slices(L):
    return [tuple(1 if b else -1 for b in bits)
            for bits in product((True, False), repeat=L)]


def w_gamma(s, gamma):
    return math.exp(gamma * sum(s[j] * s[j + 1] for j in range(len(s) - 1)))


def kernel(L, beta, gamma):
    ss = slices(L)
    n = len(ss)
    K = np.zeros((n, n))
    for i, s in enumerate(ss):
        for j, t in enumerate(ss):
            K[i, j] = math.exp(beta * sum(a * b for a, b in zip(s, t)))
    d = np.array([math.sqrt(w_gamma(s, gamma)) for s in ss])
    return ss, d[:, None] * K * d[None, :]


def gate_G18():
    print("G18  strip identity: <v, T^n v> == half-dressed strip Gibbs sum")
    obs = [("ind0", lambda s: 1.0 if s[0] == 1 else 0.0),
           ("spin0", lambda s: float(s[0])),
           ("spin1", lambda s: float(s[1]) if len(s) > 1 else float(s[0]))]
    for beta, gamma in [(0.10, 0.10), (0.12, 0.08)]:
        for L, n in [(2, 3), (3, 2), (3, 3)]:
            ss, T = kernel(L, beta, gamma)
            for name, f in obs:
                v = np.array([f(s) for s in ss])
                lhs = float(v @ np.linalg.matrix_power(T, n) @ v)
                rhs = 0.0
                for path in product(range(len(ss)), repeat=n + 1):
                    term = (f(ss[path[0]]) * f(ss[path[n]])
                            * math.sqrt(w_gamma(ss[path[0]], gamma))
                            * math.sqrt(w_gamma(ss[path[n]], gamma)))
                    for k in range(1, n):
                        term *= w_gamma(ss[path[k]], gamma)
                    for k in range(n):
                        s, t = ss[path[k]], ss[path[k + 1]]
                        term *= math.exp(beta * sum(a * b for a, b in zip(s, t)))
                    rhs += term
                rel = abs(lhs - rhs) / max(1.0, abs(rhs))
                check(rel <= 1e-10, "G18",
                      f"({beta},{gamma}) L={L} n={n} {name}: rel dev {rel:.3e}")


def spec_ratio(T):
    ev = np.linalg.eigvalsh(T)
    lam = ev[-1]
    second = max(abs(ev[0]), abs(ev[-2]))
    return second / lam


def gate_G19():
    print("G19  specRatio <= window on in-window cells (the target, measured)")
    for beta, gamma in IN_CELLS:
        window = 2.0 * math.tanh(abs(beta)) + 2.0 * math.tanh(abs(gamma))
        for L in range(2, 9):
            _, T = kernel(L, beta, gamma)
            r = spec_ratio(T)
            check(r <= window + 1e-9, "G19",
                  f"({beta},{gamma}) L={L}: specRatio {r:.9f} <= window {window:.9f}")
    beta, gamma = CONTROL_CELL
    window = 2.0 * math.tanh(abs(beta)) + 2.0 * math.tanh(abs(gamma))
    for L in (2, 6, 8):
        _, T = kernel(L, beta, gamma)
        print(f"  [rep ] G19 control ({beta},{gamma}) L={L}: specRatio "
              f"{spec_ratio(T):.6f}, window {window:.6f} (>1: theorem silent; "
              f"reported, not judged)")


def gate_G20():
    print("G20  Z-ratio converges at rate specRatio(L), constant fitted at n=1")
    beta, gamma = 0.10, 0.10
    for L in (2, 3, 4):
        ss, T = kernel(L, beta, gamma)
        ev = np.linalg.eigvalsh(T)
        lam = ev[-1]
        sr = spec_ratio(T)
        u = np.array([math.sqrt(w_gamma(s, gamma)) for s in ss])
        def rho(n):
            return float(u @ np.linalg.matrix_power(T, n + 1) @ u) / \
                (lam * float(u @ np.linalg.matrix_power(T, n) @ u))
        rho_inf = rho(50)
        K = abs(rho(1) - rho_inf) / sr if sr > 0 else 0.0
        for n in range(2, 9):
            dev = abs(rho(n) - rho_inf)
            bound = K * sr ** n * (1.0 + 1e-8) + 1e-12
            check(dev <= bound, "G20",
                  f"L={L} n={n}: |rho_n - rho_inf| {dev:.3e} <= {bound:.3e}")


def main():
    print("judge_dobrushin_d6 -- gates G18/G19/G20 for the spectral rung")
    print(f"mode: {'optimized' if sys.flags.optimize else 'normal'}")
    print("convention: T = diag(sqrt w_gamma) K_beta diag(sqrt w_gamma), free")
    print("spatial boundary, w_gamma(s) = exp(gamma sum s_j s_{j+1}),")
    print("K_beta(s,t) = exp(beta sum s_j t_j)")
    print()
    gate_G18()
    print()
    gate_G19()
    print()
    gate_G20()
    print()
    expected = 2 * 3 * 3 + 3 * 7 + 3 * 7
    print(f"checks performed: {CHECKS} (expected {expected})")
    if CHECKS < expected:
        print("VERDICT: FAIL -- fewer checks ran than expected")
        return 1
    if FAILURES:
        print(f"VERDICT: FAIL -- {len(FAILURES)} failure(s):")
        for f in FAILURES:
            print(f"  {f}")
        return 1
    print("VERDICT: PASS -- the strip identity is exact, the window sits "
          "above specRatio on every in-window cell measured, and the "
          "prefactor converges at the per-extent rate")
    return 0


if __name__ == "__main__":
    sys.exit(main())
