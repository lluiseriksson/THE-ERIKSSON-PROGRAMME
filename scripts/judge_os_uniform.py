#!/usr/bin/env python3
"""OS-R judges G1-G6 (charter docs/OS-RECONSTRUCTION-CHARTER.md, 2026-08-04).

NOT to be confused with scripts/judge_os_reconstruction.py, which is paper
14's pre-registered gate (another desk, commit 7e744e6a8).

Independent Python implementations of the OS-R design formulas -- written
from the charter, NOT from the Lean sources.  Deterministic (no RNG).
Runs identically under `python` and `python -O`: no decision depends on
`assert`.  PASS is emitted only after an explicit check counter matches
the explicit registered expectation.  Exit code 0 iff every check passed
AND the count matches.

Model: slices sigma in {+1,-1}^S (S sites), encoded as bitmasks.
  sliceW(sigma; gamma)   = exp(gamma * sum_{i<S-1} s_i s_{i+1})   [spatial chain]
  K(sigma,tau; beta)     = exp(beta  * sum_i s_i t_i)             [temporal bond]
  S_w = diag(sqrt w) K diag(sqrt w)                               [symmetrised]
  gibbs weight of a strip X_0..X_N = prod_t w(X_t) * prod_t K(X_t, X_{t+1})
  half of depth m = (a_0..a_m), W(a) = prod_t w(a_t) * prod_{t<m} K(a_t,a_{t+1})
  bond pairing (sep 2m+1): sum_{a,b} W(a) K(am,bm) W(b) conj(F a) (G b)
  site pairing (sep 2m):   sum_{a,b: am=bm} W(a) W(b) / w(am) conj(F a) (G b)
  collapse (Phi F)(sigma) = sum_{a: am=sigma} W(a) F(a)
  site form on boundary vectors: <u,v>_site = sum_sigma conj(u) v / w
  forced operator: (T v)(sigma) = w(sigma) * sum_tau K(sigma,tau) v(tau)
  unitary Q: eucl -> site, (Q u) = sqrt(w) * u
  tiltKernel = S_w / lam  (lam = Perron eigenvalue)
"""

import itertools
import math
import sys

TOL = 1e-9

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
        print(f"  FAIL  {name}")


def close(a, b, tol=TOL):
    if isinstance(a, complex) or isinstance(b, complex):
        d = abs(complex(a) - complex(b))
        m = max(abs(complex(a)), abs(complex(b)), 1.0)
        return d <= tol * m
    d = abs(a - b)
    m = max(abs(a), abs(b), 1.0)
    return d <= tol * m


def spins(sigma, S):
    return [1 if (sigma >> i) & 1 else -1 for i in range(S)]


def slice_w(sigma, S, gamma):
    s = spins(sigma, S)
    return math.exp(gamma * sum(s[i] * s[i + 1] for i in range(S - 1)))


def kern(sigma, tau, S, beta):
    s, t = spins(sigma, S), spins(tau, S)
    return math.exp(beta * sum(s[i] * t[i] for i in range(S)))


def mat_mul(A, B):
    n = len(A)
    return [[sum(A[i][k] * B[k][j] for k in range(n)) for j in range(n)]
            for i in range(n)]


def mat_vec(A, v):
    n = len(A)
    return [sum(A[i][k] * v[k] for k in range(n)) for i in range(n)]


def mat_pow(A, p):
    n = len(A)
    R = [[1.0 if i == j else 0.0 for j in range(n)] for i in range(n)]
    for _ in range(p):
        R = mat_mul(R, A)
    return R


def eig_sym(A):
    """Eigenvalues of a real symmetric matrix by cyclic Jacobi rotations."""
    n = len(A)
    M = [row[:] for row in A]
    for _ in range(6000):
        off = 0.0
        p = q = 0
        big = -1.0
        for i in range(n):
            for j in range(i + 1, n):
                off += M[i][j] ** 2
                if abs(M[i][j]) > big:
                    big, p, q = abs(M[i][j]), i, j
        if off < 1e-28:
            break
        app, aqq, apq = M[p][p], M[q][q], M[p][q]
        if apq == 0.0:
            continue
        theta = 0.5 * math.atan2(2 * apq, app - aqq)
        c, s = math.cos(theta), math.sin(theta)
        for k in range(n):
            mpk, mqk = M[p][k], M[q][k]
            M[p][k] = c * mpk + s * mqk
            M[q][k] = -s * mpk + c * mqk
        for k in range(n):
            mkp, mkq = M[k][p], M[k][q]
            M[k][p] = c * mkp + s * mkq
            M[k][q] = -s * mkp + c * mkq
    return sorted((M[i][i] for i in range(n)), reverse=True)


def perron(A, iters=2000):
    """Perron eigenvalue and unit eigenvector of a positive symmetric
    matrix (power method, deterministic uniform start)."""
    n = len(A)
    v = [1.0] * n
    for _ in range(iters):
        w_ = mat_vec(A, v)
        mx = max(abs(x) for x in w_)
        v = [x / mx for x in w_]
    nrm = math.sqrt(sum(x * x for x in v))
    v = [x / nrm for x in v]
    Av = mat_vec(A, v)
    lam = sum(v[i] * Av[i] for i in range(n))
    return lam, v


def halves(nconf, m):
    return itertools.product(range(nconf), repeat=m + 1)


def half_weight(a, S, beta, gamma):
    w_ = 1.0
    for t in a:
        w_ *= slice_w(t, S, gamma)
    for t in range(len(a) - 1):
        w_ *= kern(a[t], a[t + 1], S, beta)
    return w_


def obs_F(a, S):
    """Deterministic whole-half observable: product of site-0 spins over
    the half, plus i times the boundary site-0 spin (complex; depends on
    the WHOLE half, not only the boundary)."""
    p = 1.0
    for t in a:
        p *= spins(t, S)[0]
    return complex(p, spins(a[-1], S)[0])


def obs_G(a, S):
    """Second deterministic observable: spin sum of the first slice times
    the boundary parity."""
    s0 = sum(spins(a[0], S))
    par = 1.0
    for x in spins(a[-1], S):
        par *= x
    return complex(s0 * par, 0.25 * s0)


def run_case(S, beta, gamma, in_window):
    nconf = 2 ** S
    tag = f"S={S},b={beta},g={gamma}"
    w = [slice_w(s, S, gamma) for s in range(nconf)]
    K = [[kern(s, t, S, beta) for t in range(nconf)] for s in range(nconf)]
    sqw = [math.sqrt(x) for x in w]
    Ssym = [[sqw[i] * K[i][j] * sqw[j] for j in range(nconf)]
            for i in range(nconf)]

    # ---- G1: collapse factorisation, both parities, m = 1 ----
    m = 1
    Hs = list(halves(nconf, m))
    W = {a: half_weight(a, S, beta, gamma) for a in Hs}
    F = {a: obs_F(a, S) for a in Hs}
    G = {a: obs_G(a, S) for a in Hs}
    PhiF = [sum(W[a] * F[a] for a in Hs if a[-1] == s) for s in range(nconf)]
    PhiG = [sum(W[a] * G[a] for a in Hs if a[-1] == s) for s in range(nconf)]
    bond_bf = sum(W[a] * K[a[-1]][b[-1]] * W[b] * F[a].conjugate() * G[b]
                  for a in Hs for b in Hs)
    bond_fc = sum(PhiF[s].conjugate() * K[s][t] * PhiG[t]
                  for s in range(nconf) for t in range(nconf))
    check(f"G1 bond collapse [{tag}]", close(bond_bf, bond_fc))
    site_bf = sum(W[a] * W[b] / w[a[-1]] * F[a].conjugate() * G[b]
                  for a in Hs for b in Hs if a[-1] == b[-1])
    site_fc = sum(PhiF[s].conjugate() * PhiG[s] / w[s] for s in range(nconf))
    check(f"G1 site collapse [{tag}]", close(site_bf, site_fc))

    # ---- G2: the forced operator ----
    T = [[w[i] * K[i][j] for j in range(nconf)] for i in range(nconf)]

    def site_form(u, v):
        return sum(u[s].conjugate() * v[s] / w[s] for s in range(nconf))

    def bond_form(u, v):
        return sum(u[s].conjugate() * K[s][t] * v[t]
                   for s in range(nconf) for t in range(nconf))

    ok_def = ok_sa = True
    for i in range(nconf):
        u = [complex(1.0) if s == i else complex(0.0) for s in range(nconf)]
        for j in range(nconf):
            v = [complex(1.0) if s == j else complex(0.0)
                 for s in range(nconf)]
            Tv = [sum(T[s][t] * v[t] for t in range(nconf))
                  for s in range(nconf)]
            Tu = [sum(T[s][t] * u[t] for t in range(nconf))
                  for s in range(nconf)]
            if not close(site_form(u, Tv), bond_form(u, v)):
                ok_def = False
            if not close(site_form(u, Tv), site_form(Tu, v)):
                ok_sa = False
    check(f"G2 defining equation site(u,Tv)=bond(u,v) [{tag}]", ok_def)
    check(f"G2 site-self-adjointness at this beta [{tag}]", ok_sa)
    if beta >= 0:
        evs = eig_sym(Ssym)
        check(f"G2 site-PSD at beta>=0 [{tag}]", evs[-1] >= -TOL)

    # ---- G3: the unitary ----
    ok_iso = True
    for i in range(nconf):
        for j in range(nconf):
            u = [complex(1.0) if s == i else complex(0.0)
                 for s in range(nconf)]
            v = [complex(1.0) if s == j else complex(0.0)
                 for s in range(nconf)]
            Qu = [sqw[s] * u[s] for s in range(nconf)]
            Qv = [sqw[s] * v[s] for s in range(nconf)]
            eucl = sum(u[s].conjugate() * v[s] for s in range(nconf))
            if not close(site_form(Qu, Qv), eucl):
                ok_iso = False
    check(f"G3 Q isometry eucl->site [{tag}]", ok_iso)
    ok_conj = all(
        close(T[i][j] * sqw[j] / sqw[i], Ssym[i][j])
        for i in range(nconf) for j in range(nconf))
    check(f"G3 Q^-1 T Q = symmetrised kernel, entrywise [{tag}]", ok_conj)

    # ---- G4: the feed alignment ----
    lam, Om = perron(Ssym)
    tilt = [[Ssym[i][j] / lam for j in range(nconf)] for i in range(nconf)]
    ok_perron = all(
        close(sum(tilt[i][j] * Om[j] for j in range(nconf)), Om[i], 1e-7)
        for i in range(nconf))
    check(f"G4 tiltKernel Perron condition [{tag}]", ok_perron)
    evs = eig_sym(tilt)
    check(f"G4 top eigenvalue of tiltKernel is 1 [{tag}]",
          close(evs[0], 1.0, 1e-7))
    proj_r = max((abs(e) for e in evs[1:]), default=0.0)

    # ---- G5: n-step identification + connected bound, N = 1..4 ----
    A = [complex(spins(s, S)[0], 0.5) for s in range(nconf)]
    B = [complex(sum(spins(s, S)), -0.25) for s in range(nconf)]
    da = [sqw[s] * A[s] for s in range(nconf)]
    db = [sqw[s] * B[s] for s in range(nconf)]
    d1 = [sqw[s] for s in range(nconf)]
    for N in (1, 2, 3, 4):
        raw = complex(0.0)
        zed = 0.0
        rawA = complex(0.0)
        rawB = complex(0.0)
        for X in itertools.product(range(nconf), repeat=N + 1):
            gw = 1.0
            for t in X:
                gw *= slice_w(t, S, gamma)
            for t in range(N):
                gw *= kern(X[t], X[t + 1], S, beta)
            raw += gw * A[X[0]].conjugate() * B[X[N]]
            rawA += gw * A[X[0]].conjugate()
            rawB += gw * B[X[N]]
            zed += gw
        SN = mat_pow(Ssym, N)
        dressed = sum(da[i].conjugate() * SN[i][j] * db[j]
                      for i in range(nconf) for j in range(nconf))
        check(f"G5 dressing identity N={N} [{tag}]", close(raw, dressed))
        zed_op = sum(d1[i] * SN[i][j] * d1[j]
                     for i in range(nconf) for j in range(nconf))
        check(f"G5 partition identity N={N} [{tag}]", close(zed, zed_op))
        conn = raw / zed - (rawA / zed) * (rawB / zed)
        # Full expansion (the D-6 tilt lesson: vacuum cross terms do NOT
        # vanish).  With S^N = lam^N (P_Om + R), ||R|| <= r^N:
        #   conn * (zed/lam^N)^2 =
        #     a*b*Y + X*c1^2 + X*Y - a*c1*V - U*b*c1 - U*V
        # where a=<da,Om>, b=<Om,db>, c1=<Om,d1>, X=<pa,R pb>,
        # Y=<p1,R p1>, U=<pa,R p1>, V=<p1,R pb>.  Bound each factor.
        aOm = sum(da[s].conjugate() * Om[s] for s in range(nconf))
        bOm = sum(Om[s] * db[s] for s in range(nconf))
        c1 = sum(Om[s] * d1[s] for s in range(nconf))
        pa = [da[s] - Om[s] * sum(Om[t] * da[t] for t in range(nconf))
              for s in range(nconf)]
        pb = [db[s] - Om[s] * sum(Om[t] * db[t] for t in range(nconf))
              for s in range(nconf)]
        p1 = [d1[s] - Om[s] * c1 for s in range(nconf)]
        na = math.sqrt(sum(abs(x) ** 2 for x in pa))
        nb = math.sqrt(sum(abs(x) ** 2 for x in pb))
        n1 = math.sqrt(sum(abs(x) ** 2 for x in p1))
        rN = proj_r ** N
        num = (abs(aOm) * abs(bOm) * n1 * n1 * rN
               + na * nb * c1 * c1 * rN
               + na * nb * n1 * n1 * rN * rN
               + abs(aOm) * c1 * n1 * nb * rN
               + na * n1 * abs(bOm) * c1 * rN
               + na * nb * n1 * n1 * rN * rN)
        z_ratio = zed / (lam ** N)
        bound = num / (z_ratio * z_ratio)
        check(f"G5 connected bound N={N} [{tag}]",
              abs(conn) <= bound + 1e-7 * max(1.0, bound))

    # ---- G6: window / RP overlap ----
    if in_window:
        win = 2 * math.tanh(abs(beta)) + 2 * math.tanh(abs(gamma))
        check(f"G6 window value {win:.4f} <= 0.8 [{tag}]", win <= 0.8)
        check(f"G6 RP half-plane beta >= 0 [{tag}]", beta >= 0)
        check(f"G6 projected ratio r={proj_r:.6f} <= 0.999 [{tag}]",
              proj_r <= 0.999)


def main():
    cases = [
        (2, 0.2, 0.2, True),    # in-window, RP: the composition witness
        (3, 0.2, 0.2, True),    # same, larger slice
        (2, 0.5, 0.3, False),   # outside window: identities still hold
        (2, -0.3, 0.4, False),  # negative beta: self-adjoint without PSD
        (3, 0.7, -0.2, False),  # negative gamma weight
    ]
    for S, b, g, iw in cases:
        print(f"case S={S} beta={b} gamma={g} window={iw}")
        run_case(S, b, g, iw)

    # Registered expectation: per case = G1(2) + G2(2 or 3) + G3(2) +
    # G4(2) + G5(12); in-window adds G6(3).  Cases 1,2 have beta>=0 ->
    # G2 = 3 and G6 = 3 -> 24 each; case 3 beta>=0 -> 21; case 4
    # beta<0 -> 20; case 5 beta>=0 -> 21.  Total = 24+24+21+20+21 = 110.
    expected = 110
    total = passed + failed
    print("=" * 64)
    print(f"checks run: {total}  passed: {passed}  failed: {failed}  "
          f"expected: {expected}")
    if failures:
        print("failures:")
        for f in failures:
            print(f"  - {f}")
    if failed == 0 and total == expected:
        print("JUDGE VERDICT: PASS (all checks, count matches registration)")
        return 0
    if failed == 0 and total != expected:
        print("JUDGE VERDICT: FAIL (count mismatch against registration)")
        return 2
    print("JUDGE VERDICT: FAIL")
    return 1


if __name__ == "__main__":
    sys.exit(main())
