#!/usr/bin/env python3
"""D-6b gates, registered WITH docs/DOBRUSHIN-D6-B2-DESIGN.md, BEFORE any
Lean of B-2/B-3.  Lineage: judge_dobrushin_d6.py (G18-G20 passed 60/60 both
modes, ledger Addendum 594); charter Amendments 1-2.

  G21  THE B-2 IDENTITY, abstractly: connCorr of the packaged operator
       equals (sum Om^2) times the band covariance of f_v = v/Om, exactly,
       on registered symmetric positive-ENTRY matrices including one whose
       subdominant eigenvalue is NEGATIVE (the no-spectral-positivity
       failure mode of Amendment 2, kept visibly alive).
  G22  THE TILT ALGEBRA, exactly, on the coupled Z2 kernel: the band
       measure is the free strip Gibbs measure tilted at the two ends by
       psi = Om / sqrt(w)  (NOT Om*sqrt(w) -- the dressing-conflation
       failure mode); the five-term covariance decomposition; the
       denominator floor (min psi)^2.
  G23  THE COROLLARY'S NUMERIC SHADOW: the D-5 feed (oscillation-sum
       bound at rate alpha^n, every end-slice site pair at distance >= n)
       at the four tilt observables, and the ASSEMBLED C_{L,f} alpha^n
       bound over the measured band covariance -- the composed-prefactor-
       finite claim, measured before any Lean depends on it.

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


IN_CELLS = [(0.10, 0.10), (0.12, 0.08)]


# ----------------------------------------------------------------------
# shared machinery


def perron(T):
    """Perron pair of a symmetric matrix with strictly positive entries.
    Guard (not a check): the eigenvector must come out strictly one-signed."""
    ev, evec = np.linalg.eigh(T)
    lam = ev[-1]
    Om = evec[:, -1]
    if Om[0] < 0:
        Om = -Om
    if min(Om) <= 0:
        raise SystemExit("FATAL: Perron vector not strictly positive -- "
                         "wrong test matrix, refusing to judge with it")
    if lam <= 0:
        raise SystemExit("FATAL: Perron eigenvalue not positive")
    return lam, Om


def band_pair_sum(M, Om, f, g, n):
    """sum over paths of f(x0) g(xn) * bandW, bandW = Om(x0) prod M Om(xn)."""
    m = len(Om)
    tot = 0.0
    for path in product(range(m), repeat=n + 1):
        term = f[path[0]] * g[path[-1]] * Om[path[0]] * Om[path[-1]]
        for k in range(n):
            term *= M[path[k], path[k + 1]]
        tot += term
    return tot


def band_cov(M, Om, f, g, n):
    s2 = float(np.dot(Om, Om))
    Ef = float(np.dot(f * Om, Om)) / s2
    Eg = float(np.dot(g * Om, Om)) / s2
    return band_pair_sum(M, Om, f, g, n) / s2 - Ef * Eg


# ----------------------------------------------------------------------
# G21


def g21_matrices():
    A = np.zeros((4, 4))
    for i in range(4):
        for j in range(4):
            A[i, j] = 0.3 + ((i * 7 + j * 3) % 5) * 0.15
    A = (A + A.T) / 2.0
    B = np.zeros((5, 5))
    for i in range(5):
        for j in range(5):
            B[i, j] = 0.2 + ((i * i + 3 * j) % 7) * 0.1
    B = (B + B.T) / 2.0
    C = np.full((4, 4), 0.05)
    for i in range(4):
        C[i, 3 - i] = 2.0
    return [("A4", A), ("B5", B), ("Canti", C)]


def gate_G21():
    print("G21  connCorr == (sum Om^2) * bandCov(f_v), exactly")
    mats = g21_matrices()
    neg_seen = False
    for name, T in mats:
        lam, Om = perron(T)
        M = T / lam
        ev = np.linalg.eigvalsh(M)
        if ev[0] < -1e-6:
            neg_seen = True
        m = T.shape[0]
        vac = Om / math.sqrt(float(np.dot(Om, Om)))
        obs = [("e0", np.eye(m)[0]),
               ("vdet", np.array([0.7, -0.3, 0.5, 0.2, -0.6][:m])),
               ("vperp", np.eye(m)[0]
                - (float(np.dot(Om, np.eye(m)[0]))
                   / float(np.dot(Om, Om))) * Om)]
        s2 = float(np.dot(Om, Om))
        for oname, v in obs:
            f_v = v / Om
            for n in range(5):
                lhs = float(v @ np.linalg.matrix_power(M, n) @ v) \
                    - float(np.dot(vac, v)) ** 2
                rhs = s2 * band_cov(M, Om, f_v, f_v, n)
                dev = abs(lhs - rhs) / max(1.0, abs(lhs))
                check(dev <= 1e-10, "G21",
                      f"{name} {oname} n={n}: rel dev {dev:.3e}")
    check(neg_seen, "G21",
          "at least one registered matrix has a NEGATIVE subdominant "
          "eigenvalue (spectral positivity is NOT smuggled in)")


# ----------------------------------------------------------------------
# G22 / G23 -- the coupled Z2 kernel, same convention as judge d6


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
    return ss, K, d, d[:, None] * K * d[None, :]


def free_strip_stats(ss, K, wvec, obs0, obsn, n):
    """One enumeration pass over the free strip measure
    gibbsW = prod_t w(X_t) * prod_steps K.  Returns E[F] for every F in the
    dictionary built from obs0 (slice 0) and obsn (slice n) pairs."""
    m = len(ss)
    Z = 0.0
    sums = {}
    keys0 = list(obs0.keys())
    keysn = list(obsn.keys())
    for k0 in keys0:
        sums[(k0, None)] = 0.0
    for kn in keysn:
        sums[(None, kn)] = 0.0
    for k0 in keys0:
        for kn in keysn:
            sums[(k0, kn)] = 0.0
    for path in product(range(m), repeat=n + 1):
        gw = 1.0
        for k in range(n + 1):
            gw *= wvec[path[k]]
        for k in range(n):
            gw *= K[path[k], path[k + 1]]
        Z += gw
        for k0 in keys0:
            a0 = obs0[k0][path[0]]
            sums[(k0, None)] += a0 * gw
        for kn in keysn:
            bn = obsn[kn][path[-1]]
            sums[(None, kn)] += bn * gw
        for k0 in keys0:
            a0 = obs0[k0][path[0]]
            for kn in keysn:
                sums[(k0, kn)] += a0 * obsn[kn][path[-1]] * gw
    return {key: val / Z for key, val in sums.items()}


def osc_sum(ss, L, vals):
    """sum over slice sites of the oscillation of a slice observable:
    deltaAt i = max |vals(s) - vals(s')| over slice pairs differing at i."""
    idx = {s: k for k, s in enumerate(ss)}
    total = 0.0
    for i in range(L):
        d = 0.0
        for s in ss:
            s2 = list(s)
            s2[i] = -s2[i]
            d = max(d, abs(vals[idx[s]] - vals[idx[tuple(s2)]]))
        total += d
    return total


def gate_G22_G23():
    print("G22  tilt algebra (psi = Om/sqrt w): identity, five-term "
          "decomposition, denominator floor")
    print("G23  D-5 feed at the tilt observables + assembled "
          "C_{L,f} alpha^n over the measured band covariance")
    for beta, gamma in IN_CELLS:
        alpha = 2.0 * math.tanh(abs(beta)) + 2.0 * math.tanh(abs(gamma))
        for L in (2, 3):
            ss, K, d, T = kernel(L, beta, gamma)
            lam, Om = perron(T)
            M = T / lam
            wvec = np.array([w_gamma(s, gamma) for s in ss])
            psi = Om / d
            fobs = np.array([float(s[0]) for s in ss])
            a = fobs * psi
            for n in (2, 3, 4):
                st = free_strip_stats(
                    ss, K, wvec,
                    {"a": a, "p": psi}, {"b": a, "q": psi}, n)
                Ea, Ep = st[("a", None)], st[("p", None)]
                Eb, Eq = st[(None, "b")], st[(None, "q")]
                Epq = st[("p", "q")]
                Cab = st[("a", "b")] - Ea * Eb
                Cpq = Epq - Ep * Eq
                Caq = st[("a", "q")] - Ea * Eq
                Cpb = st[("p", "b")] - Ep * Eb
                bc = band_cov(M, Om, fobs, fobs, n)
                # (a) the tilt identity for the two-endpoint expectation
                s2 = float(np.dot(Om, Om))
                Eband_fg = band_pair_sum(M, Om, fobs, fobs, n) / s2
                tilt_fg = st[("a", "b")] / Epq
                dev = abs(Eband_fg - tilt_fg) / max(1.0, abs(tilt_fg))
                check(dev <= 1e-10, "G22",
                      f"({beta},{gamma}) L={L} n={n} identity: "
                      f"rel dev {dev:.3e}")
                # (b) the five-term decomposition
                num = (Cab * Cpq + Cab * Ep * Eq + Ea * Eb * Cpq
                       - Caq * Cpb - Caq * Ep * Eb - Ea * Eq * Cpb)
                dev5 = abs(bc - num / Epq ** 2) / max(1.0, abs(bc))
                check(dev5 <= 1e-10, "G22",
                      f"({beta},{gamma}) L={L} n={n} five-term: "
                      f"rel dev {dev5:.3e}")
                # (c) the denominator floor
                floor = float(min(psi)) ** 2
                check(Epq >= floor - 1e-12, "G22",
                      f"({beta},{gamma}) L={L} n={n} floor: "
                      f"E[pq] {Epq:.6f} >= (min psi)^2 {floor:.6f}")
                # G23 (i) the D-5 feed at the four covariances
                Sa = osc_sum(ss, L, a)
                Sp = osc_sum(ss, L, psi)
                rate = alpha ** n / (4.0 * (1.0 - alpha))
                for cname, cval, s0, sn in (
                        ("ab", Cab, Sa, Sa), ("pq", Cpq, Sp, Sp),
                        ("aq", Caq, Sa, Sp), ("pb", Cpb, Sp, Sa)):
                    bnd = s0 * sn * rate
                    check(abs(cval) <= bnd * (1.0 + 1e-8) + 1e-12, "G23",
                          f"({beta},{gamma}) L={L} n={n} feed {cname}: "
                          f"|C| {abs(cval):.3e} <= {bnd:.3e}")
                # G23 (ii) the assembled bound
                Ma = float(max(abs(a)))
                Mp = float(max(abs(psi)))
                Bab = Sa * Sa / (4.0 * (1.0 - alpha))
                Bpq = Sp * Sp / (4.0 * (1.0 - alpha))
                Baq = Sa * Sp / (4.0 * (1.0 - alpha))
                Bpb = Sp * Sa / (4.0 * (1.0 - alpha))
                CLf = (Bab * Bpq + Bab * Mp * Mp + Ma * Ma * Bpq
                       + Baq * Bpb + Baq * Mp * Ma + Ma * Mp * Bpb) \
                    / float(min(psi)) ** 4
                bnd = CLf * alpha ** n
                check(abs(bc) <= bnd * (1.0 + 1e-8) + 1e-12, "G23",
                      f"({beta},{gamma}) L={L} n={n} assembled: "
                      f"|bandCov| {abs(bc):.3e} <= C_Lf alpha^n {bnd:.3e}")


def main():
    print("judge_dobrushin_d6b -- gates G21/G22/G23 for B-2/B-3")
    print(f"mode: {'optimized' if sys.flags.optimize else 'normal'}")
    print("convention: T = diag(sqrt w_gamma) K_beta diag(sqrt w_gamma), free")
    print("spatial boundary; band weight = Om(x0) prod (T/lam) Om(xn); tilt")
    print("psi = Om / sqrt(w_gamma); free strip measure = prod_t w(X_t) *")
    print("prod_steps K_beta (paper 9's gibbsWeight = the D-5 rectangle)")
    print()
    gate_G21()
    print()
    gate_G22_G23()
    print()
    expected = (3 * 3 * 5 + 1) + 2 * 2 * 3 * (3 + 5)
    print(f"checks performed: {CHECKS} (expected {expected})")
    if CHECKS < expected:
        print("VERDICT: FAIL -- fewer checks ran than expected")
        return 1
    if FAILURES:
        print(f"VERDICT: FAIL -- {len(FAILURES)} failure(s):")
        for f in FAILURES:
            print(f"  {f}")
        return 1
    print("VERDICT: PASS -- the B-2 identity is exact (including on a "
          "negative-subdominant matrix), the tilt algebra is exact with "
          "psi = Om/sqrt(w), the D-5 feed holds at the tilt observables, "
          "and the assembled per-extent prefactor bounds the measured "
          "band covariance")
    return 0


if __name__ == "__main__":
    sys.exit(main())
