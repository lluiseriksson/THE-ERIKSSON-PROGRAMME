# audit_page_pass2_numeric.py -- INDEPENDENT AUDIT DESK, STEP 1
# Written WITHOUT reading scripts/derive_page_pass2.py (regime point 4).
# Direct 2D numerical integration of the five moments over [-pi,pi]^2
# using ORIGINAL Bessel definitions (mpmath.besseli), no saddle expansion.
#
# Definitions audited (conv:mass, unnormalized, [-pi,pi]^2):
#   c = cos(t/4), z_s = 4*beta*c, C = 2c^2-1
#   x = cos s, y = cos alpha; P=(1-x)/2, Q=(1-y)/2; D = x+y
#   N = C(2x^2-1) + y(Cx - 1 + x^2)
#   R^2 = 4(c^2(1-P-Q) + PQ); z = 2*beta*sqrt(R^2)
#   K = 2*beta*I1(z)/z ; H_B = I2(z)/z^2
#   mu_f = II K f ; nu_f = II D f H_B
#   Xhat = 4 b^3 (mu_D nu_N - mu_N nu_D)/mu_D^2
#   r(z) = I2/(z I1), rs = r(z_s), dr = r - rs
#   Xhat_1 = 2 b^2 rs (mu_D <DN>_K - mu_N <D^2>_K)/mu_D^2
#   Xhat_2 = 2 b^2 (mu_D <DN dr>_K - mu_N <D^2 dr>_K)/mu_D^2
# Judges: b*Xhat_1 -> 2T(c), b*Xhat_2 -> -T(c), b*Xhat -> T(c),
#   T(c) = (4c^2-1)/(8c^3).
# Claimed 1/beta coefficients (C2):
#   r2   = (-8c^4+15c^2-4)/(32 c^6)
#   r2_1 = (-44c^4+29c^2-6)/(32 c^6)
#   r2_2 = (18c^4-7c^2+1)/(16 c^6)
#
# Conditioning: all moments carry the common constant factor e^{-z_s}
# (equivalent to using exp(z - z_s) with e^{-z}-scaled Bessels; in
# exact arithmetic the constant cancels in every ratio). All summed
# quantities are O(1)-conditioned relative to each other; mpmath keeps
# full relative precision on the huge intermediates regardless.
#
# Quadrature: panel-subdivided Gauss-Legendre, nodes refined to full
# working precision by Newton iteration on Legendre polynomials
# (float64 seed from numpy). Panels geometric from the saddle scale
# h = 1/sqrt(beta*c). Integrand even in s and alpha separately, so
# integrate [0,pi]^2 and multiply by 4. Nodes with z_s - z > 140 are
# skipped (contribution < e^{-140} * poly, utterly negligible vs
# moments ~ 1e-4..1e0 relative scale).

import time
from mpmath import mp, mpf, cos, sqrt, exp, besseli, pi, legendre, nstr
import numpy as np

mp.dps = 30

LOGPATH = r"C:\Users\lluis\AppData\Local\Temp\eriksson-push2\scripts\audit_page_pass2_transcript.txt"
logf = open(LOGPATH, "a", encoding="utf-8")
def log(s=""):
    print(s, flush=True)
    logf.write(s + "\n")
    logf.flush()

def fs(v, n=12):
    return nstr(mpf(v), n)

# ---------- Gauss-Legendre nodes at full precision ----------
_gl_cache = {}
def gl_nodes(n):
    if n in _gl_cache:
        return _gl_cache[n]
    xs, _ = np.polynomial.legendre.leggauss(n)
    out = []
    for x0 in xs:
        x = mpf(repr(float(x0)))
        for _ in range(100):
            Pn = legendre(n, x)
            Pn1 = legendre(n - 1, x)
            dP = n * (x * Pn - Pn1) / (x * x - 1)
            dx = Pn / dP
            x = x - dx
            if abs(dx) < mpf(10) ** (-(mp.dps + 8)):
                break
        Pn = legendre(n, x)
        Pn1 = legendre(n - 1, x)
        dP = n * (x * Pn - Pn1) / (x * x - 1)
        w = 2 / ((1 - x * x) * dP * dP)
        out.append((x, w))
    _gl_cache[n] = out
    return out

def nodes_1d(bpts, n):
    base = gl_nodes(n)
    out = []
    for i in range(len(bpts) - 1):
        a, b = bpts[i], bpts[i + 1]
        half = (b - a) / 2
        mid = (a + b) / 2
        for (u, w) in base:
            out.append((mid + half * u, half * w))
    return out

def breakpoints(beta, c, refine=1):
    h = 1 / sqrt(beta * c) / refine
    b = [mpf(0)]
    m = h
    while m < mp.pi * mpf("0.999"):
        b.append(m)
        m = m * 2
    b.append(mp.pi)
    return b

# ---------- one cell ----------
def compute_cell(t, beta, n=24, refine=1, skip_thresh=mpf(140)):
    t = mpf(t)
    beta = mpf(beta)
    c = cos(t / 4)
    zs = 4 * beta * c
    C = 2 * c * c - 1
    Escale = exp(-zs)          # common conditioning constant e^{-z_s}
    rs = besseli(2, zs) / (zs * besseli(1, zs))
    bpts = breakpoints(beta, c, refine)
    nod = nodes_1d(bpts, n)
    xw = [(cos(s), w) for (s, w) in nod]
    S = [mpf(0)] * 8   # mu_D, mu_N, <DN>_K, <D2>_K, <DNdr>_K, <D2dr>_K, nu_N, nu_D
    neval = 0
    nskip = 0
    cc = c * c
    for (x, wx) in xw:
        P = (1 - x) / 2
        for (y, wy) in xw:
            Q = (1 - y) / 2
            R2 = 4 * (cc * (1 - P - Q) + P * Q)
            if R2 < 0:
                R2 = mpf(0)
            z = 2 * beta * sqrt(R2)
            if zs - z > skip_thresh:
                nskip += 1
                continue
            neval += 1
            w = wx * wy
            I1 = besseli(1, z)
            I2 = besseli(2, z)
            # scaled kernels (times e^{-z_s}); z > 0 at all GL nodes here
            Ktil = 2 * beta * I1 / z * Escale
            HBtil = I2 / (z * z) * Escale
            r = I2 / (z * I1)
            dr = r - rs
            D = x + y
            N = C * (2 * x * x - 1) + y * (C * x - 1 + x * x)
            KD = Ktil * D
            S[0] += w * KD
            S[1] += w * Ktil * N
            S[2] += w * KD * N
            S[3] += w * KD * D
            S[4] += w * KD * N * dr
            S[5] += w * KD * D * dr
            S[6] += w * HBtil * D * N
            S[7] += w * HBtil * D * D
    S = [4 * v for v in S]     # evenness in s and alpha
    mu_D, mu_N, mDN, mD2, mDNdr, mD2dr, nu_N, nu_D = S
    Xhat  = 4 * beta**3 * (mu_D * nu_N - mu_N * nu_D) / mu_D**2
    Xhat1 = 2 * beta**2 * rs * (mu_D * mDN - mu_N * mD2) / mu_D**2
    Xhat2 = 2 * beta**2 * (mu_D * mDNdr - mu_N * mD2dr) / mu_D**2
    return {
        "t": t, "beta": beta, "c": c, "zs": zs, "rs": rs,
        "moments": S, "Xhat": Xhat, "Xhat1": Xhat1, "Xhat2": Xhat2,
        "neval": neval, "nskip": nskip,
    }

def T_of(c):
    return (4 * c * c - 1) / (8 * c**3)

def r2_of(c):
    return (-8 * c**4 + 15 * c**2 - 4) / (32 * c**6)

def r2_1_of(c):
    return (-44 * c**4 + 29 * c**2 - 6) / (32 * c**6)

def r2_2_of(c):
    return (18 * c**4 - 7 * c**2 + 1) / (16 * c**6)

def main():
    log("=" * 78)
    log("AUDIT STEP 1 -- independent numerics (audit_page_pass2_numeric.py)")
    log("mp.dps = %d ; date 2026-07-10 ; auditor session (split-role regime pt 4)" % mp.dps)
    log("=" * 78)

    # ---- quadrature convergence check at one cell (t=1.5, beta=80) ----
    log("\n-- quadrature convergence check, cell (t=1.5, beta=80) --")
    t0 = time.time()
    A = compute_cell(1.5, 80, n=24, refine=1)
    tA = time.time() - t0
    t0 = time.time()
    B = compute_cell(1.5, 80, n=36, refine=2)
    tB = time.time() - t0
    for key in ("Xhat", "Xhat1", "Xhat2"):
        va, vb = A[key], B[key]
        rel = abs(va - vb) / abs(vb)
        log("  %-6s  n24/r1: %s   n36/r2: %s   rel.diff: %s"
            % (key, fs(va), fs(vb), fs(rel, 3)))
    log("  eval counts: A %d evals / %d skipped ; B %d / %d  (%.1fs / %.1fs)"
        % (A["neval"], A["nskip"], B["neval"], B["nskip"], tA, tB))

    # ---- main grid ----
    ts = [mpf("1.0"), mpf("1.5"), mpf("2.5")]
    betas = [mpf(40), mpf(80), mpf(160)]
    results = {}
    for t in ts:
        for b in betas:
            t0 = time.time()
            r = compute_cell(t, b, n=24, refine=1)
            results[(t, b)] = r
            log("  computed cell t=%s beta=%s  (%.1fs, %d evals, %d skipped)"
                % (fs(t, 3), fs(b, 4), time.time() - t0, r["neval"], r["nskip"]))

    log("")
    for t in ts:
        c = results[(t, betas[0])]["c"]
        T = T_of(c)
        r2 = r2_of(c)
        r21 = r2_1_of(c)
        r22 = r2_2_of(c)
        log("=" * 78)
        log("t = %s   c = %s   T(c) = %s" % (fs(t, 3), fs(c), fs(T)))
        log("  targets: 2T = %s   -T = %s" % (fs(2 * T), fs(-T)))
        log("  claimed r2   = %s" % fs(r2))
        log("  claimed r2_1 = %s ; r2_2 = %s (sum = %s)"
            % (fs(r21), fs(r22), fs(r21 + r22)))
        log("-" * 78)
        log("  %-6s %-22s %-22s %-22s" % ("beta", "b*Xhat1", "b*Xhat2", "b*Xhat (sum chk)"))
        f1 = {}; f2 = {}; f0 = {}
        for b in betas:
            r = results[(t, b)]
            v1 = b * r["Xhat1"]; v2 = b * r["Xhat2"]; v0 = b * r["Xhat"]
            f1[b], f2[b], f0[b] = v1, v2, v0
            splitchk = abs((r["Xhat1"] + r["Xhat2"] - r["Xhat"]) / r["Xhat"])
            log("  %-6s %-22s %-22s %-22s  split-id rel err %s"
                % (fs(b, 4), fs(v1), fs(v2), fs(v0), fs(splitchk, 3)))
        # Richardson (1/beta): R1 = 2 f(2b) - f(b); (1/beta^2 too): R2 from 3 pts
        b1, b2, b3 = betas
        for name, f, target in (("b*Xhat1 vs 2T", f1, 2 * T),
                                ("b*Xhat2 vs -T", f2, -T),
                                ("b*Xhat  vs  T", f0, T)):
            R1a = 2 * f[b2] - f[b1]
            R1b = 2 * f[b3] - f[b2]
            R2 = (8 * f[b3] - 6 * f[b2] + f[b1]) / 3
            log("  %s:" % name)
            log("    Rich1(40,80)=%s  Rich1(80,160)=%s  Rich2=%s  target=%s"
                % (fs(R1a), fs(R1b), fs(R2), fs(target)))
            log("    rel.err of Rich2 vs target: %s" % fs(abs(R2 - target) / abs(target), 4))
        # drift / second-order coefficient checks
        log("  second-order (1/beta) coefficient extraction:")
        for name, f, target, claim in (
                ("d1 = b*(b*Xhat1 - 2T)", f1, 2 * T, r21),
                ("d2 = b*(b*Xhat2 + T)", f2, -T, r22),
                ("d  = b*(b*Xhat  - T)", f0, T, r2)):
            d = {b: b * (f[b] - target) for b in betas}
            rich = 2 * d[b3] - d[b2]
            rich3 = (8 * d[b3] - 6 * d[b2] + d[b1]) / 3
            # drift-halving signature toward claimed value
            e1 = d[b2] - claim
            e2 = d[b3] - claim
            ratio = e1 / e2 if e2 != 0 else mpf(0)
            log("    %s:" % name)
            log("      d(40)=%s d(80)=%s d(160)=%s" % (fs(d[b1]), fs(d[b2]), fs(d[b3])))
            log("      Rich(80,160)=%s  Rich3pt=%s  CLAIM=%s  rel.err(Rich3pt)=%s"
                % (fs(rich), fs(rich3), fs(claim), fs(abs(rich3 - claim) / abs(claim), 4)))
            log("      residual-halving ratio (d(80)-claim)/(d(160)-claim) = %s (expect ~2)"
                % fs(ratio, 5))
    log("=" * 78)
    log("STEP 1 numerics complete.")

if __name__ == "__main__":
    main()
