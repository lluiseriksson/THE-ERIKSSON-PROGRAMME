#!/usr/bin/env python3
"""PRE-REGISTERED JUDGES for the CONGRUENCE lane (docs/CONGRUENCE-CHARTER.md).

Committed BEFORE being run, and before any Lean of this lane.  Neither gate has
been computed at the time of writing: the lane's earlier probes (E1-E3 in the
charter) are EVIDENCE, and under the 2026-08-01 gate rule a measurement whose
verdict I already know cannot be my judge.  These two predict NUMBERS I do not
know.

  JA  the convergence exponent      PREDICTION: p = 2, slope in [-2.10, -1.90]
  JB  positive-definiteness is      PREDICTION: >= 1 of 12 indefinite witnesses
      load-bearing                              exceeds (1-mu)/(1+mu)

  JC  (Lean; runs on Colab, not here)  PREDICTION: zero errors, zero sorry,
      standard axiom triple only, merged-core job count +1 exactly.

Instruments per the 2026-08-01 rule: no bare `assert` (python -O deletes them,
and this repo has already shipped two false PASSes that way); every check goes
through check(), which counts; PASS only after an explicit count reconciliation;
self-test in BOTH modes; the light-script contract measured, never assumed.
"""

import math
import sys
import time

import numpy as np
from scipy.optimize import minimize

# ---------------------------------------------------------------- predictions
JA_CELLS = [(3, 0.20), (4, 0.20), (5, 0.15), (4, 0.35)]
JA_GAMMAS = [1.0, 1.5, 2.0, 2.5, 3.0]
JA_SLOPE_LO, JA_SLOPE_HI = -2.10, -1.90        # PREDICTED p = 2

JB_N_WITNESSES = 12
JB_MIN_EXCEEDING = 1                            # PREDICTED at least one

CHECKS_RUN = 0
CHECKS_FAILED = []
PRECOND_FAILED = []


def check(name, condition, detail="", precondition=False):
    """A failed PRECONDITION means the case was never testable and carries no
    evidence; a failed CLAIM contradicts the prediction.  Keeping them apart is
    not pedantry: collapsing them lets a setup bug print itself as a result."""
    global CHECKS_RUN
    CHECKS_RUN += 1
    if not condition:
        (PRECOND_FAILED if precondition else CHECKS_FAILED).append(f"{name}: {detail}")
    return bool(condition)


def peak_rss_mib():
    try:
        import psutil
        return psutil.Process().memory_info().peak_wset / (1024.0 * 1024.0)
    except Exception:
        return -1.0


# ---------------------------------------------------------------------- model
def transfer(L, beta, gamma):
    """T_L = D K_beta D, D = diag(sqrt(w_gamma)); free spatial boundary."""
    n = 1 << L
    S = np.array([[1 - 2 * ((c >> j) & 1) for j in range(L)] for c in range(n)],
                 dtype=np.float64)
    wexp = gamma * (S[:, :-1] * S[:, 1:]).sum(axis=1) if L >= 2 else np.zeros(n)
    E = beta * (S @ S.T) + 0.5 * wexp[:, None] + 0.5 * wexp[None, :]
    return np.exp(E - E.max())


def ratio_of(A):
    ev = np.linalg.eigvalsh(A)
    a = np.sort(np.abs(ev))[::-1]
    return a[1] / a[0]


def r_scaled(M, logd):
    d = np.exp(logd - logd.max())
    return ratio_of(M * np.outer(d, d))


# ------------------------------------------------------------------------- JA
def gate_JA():
    print("JA  convergence exponent of  tanh(beta*L) - r(gamma)   "
          f"[PREDICTED p = 2, slope in ({JA_SLOPE_LO}, {JA_SLOPE_HI})]")
    print(f"    {'L':>3} {'beta':>6} {'tanh(bL)':>10} {'deficit@1.0':>12} "
          f"{'deficit@3.0':>12} {'slope':>9}  verdict")
    for (L, b) in JA_CELLS:
        tgt = math.tanh(b * L)
        defs = [tgt - ratio_of(transfer(L, b, g)) for g in JA_GAMMAS]
        if not check(f"JA/positive/L={L},b={b}", all(d > 1e-13 for d in defs),
                     f"deficits {defs} not all measurable", precondition=True):
            print(f"    {L:>3} {b:>6.2f}  deficit under machine noise -- NOT TESTED")
            continue
        slope = np.polyfit(JA_GAMMAS, np.log(defs), 1)[0]
        ok = check(f"JA/slope/L={L},b={b}", JA_SLOPE_LO <= slope <= JA_SLOPE_HI,
                   f"fitted slope {slope:.4f} outside the predicted band")
        print(f"    {L:>3} {b:>6.2f} {tgt:>10.6f} {defs[0]:>12.3e} "
              f"{defs[-1]:>12.3e} {slope:>9.4f}  {'ok' if ok else 'FAIL'}")


# ------------------------------------------------------------------------- JB
def gate_JB(rng):
    print(f"JB  is positive definiteness load-bearing?   "
          f"[PREDICTED >= {JB_MIN_EXCEEDING} of {JB_N_WITNESSES} exceed]")
    print(f"    {'n':>3} {'min eig':>11} {'mu':>9} {'(1-mu)/(1+mu)':>15} "
          f"{'best r':>12} {'excess':>12}  exceeds?")
    found, built = 0, 0
    tries = 0
    while built < JB_N_WITNESSES and tries < 4000:
        tries += 1
        n = int(rng.integers(4, 7))
        M = np.ones((n, n))
        off = rng.uniform(0.05, 0.95, (n, n))
        iu = np.triu_indices(n, 1)
        M[iu] = off[iu]
        M = np.triu(M) + np.triu(M, 1).T
        np.fill_diagonal(M, 1.0)
        w = np.linalg.eigvalsh(M)
        if w.min() >= -1e-9:                       # want INDEFINITE witnesses
            continue
        built += 1
        mu = M[iu].min()
        target = (1.0 - mu) / (1.0 + mu)
        best, best_x = -1.0, np.zeros(n)
        for _ in range(300):
            x = rng.normal(0.0, rng.choice([2.0, 8.0, 20.0]), n)
            v = r_scaled(M, x)
            if v > best:
                best, best_x = v, x
        starts = [best_x, np.zeros(n)]
        for (i, j) in zip(*iu):
            z = np.full(n, -30.0); z[i] = 0.0; z[j] = 0.0
            starts.append(z)
        for x0 in starts:
            res = minimize(lambda z: -r_scaled(M, z), x0, method="Nelder-Mead",
                           options={"maxiter": 1500, "maxfev": 1500,
                                    "xatol": 1e-10, "fatol": 1e-14})
            best = max(best, -res.fun)
        exceeds = best > target + 1e-9
        found += int(exceeds)
        print(f"    {n:>3} {w.min():>11.3e} {mu:>9.6f} {target:>15.9f} "
              f"{best:>12.9f} {best - target:>12.2e}  {'YES' if exceeds else 'no'}")
    check("JB/built", built == JB_N_WITNESSES,
          f"only built {built} indefinite witnesses", precondition=True)
    check("JB/exceed-count", found >= JB_MIN_EXCEEDING,
          f"{found} of {built} exceeded; predicted >= {JB_MIN_EXCEEDING}")
    print(f"    -> {found} of {built} indefinite witnesses exceed the PD bound")


# ------------------------------------------------------------------- selftest
def selftest():
    M = np.array([[1.0, 0.4], [0.4, 1.0]])
    check("selftest/2x2", abs(r_scaled(M, np.zeros(2)) - 0.6 / 1.4) < 1e-12, "2x2")
    check("selftest/tensor", abs(ratio_of(transfer(3, 0.3, 0.0)) - math.tanh(0.3)) < 1e-12,
          "gamma=0 must give tanh(beta)")
    bad = check("selftest/negative-control", abs(r_scaled(M, np.zeros(2)) - 9.0) < 1e-12,
                "DESIGNED to fail")
    if bad:
        print("SELFTEST BROKEN: the negative control passed.")
        return 1
    CHECKS_FAILED.pop()
    if CHECKS_FAILED or PRECOND_FAILED:
        print("SELFTEST FAILED:", CHECKS_FAILED, PRECOND_FAILED)
        return 1
    print(f"selftest OK in {'OPTIMISED (-O)' if not __debug__ else 'normal'} mode: "
          f"{CHECKS_RUN} checks, negative control bit as designed")
    return 0


def main():
    t0 = time.perf_counter()
    rng = np.random.default_rng(20260801)
    print("=" * 84)
    print("JUDGES — CONGRUENCE LANE   (docs/CONGRUENCE-CHARTER.md)")
    print("mode:", "OPTIMISED (-O)" if not __debug__ else "normal")
    print("=" * 84)
    gate_JA()
    print()
    gate_JB(rng)
    print()

    elapsed = time.perf_counter() - t0
    rss = peak_rss_mib()
    rss_txt = "UNMEASURED" if rss < 0 else f"{rss:.0f} MiB"
    print("=" * 84)
    print(f"CONTRACT   wall = {elapsed:.2f} s (limit 30)   peak RSS = {rss_txt} "
          f"(limit 512)   processes = 1")
    if rss < 0:
        print("           -> RSS UNMEASURED: contract NOT demonstrated")
    elif elapsed <= 30.0 and rss <= 512.0:
        print("           -> WITHIN the light-script contract (all three measured)")
    else:
        print("           -> OVER CONTRACT: this belongs on Colab")

    expected = len(JA_CELLS) * 2 + 2
    if CHECKS_RUN != expected:
        print(f"COUNT MISMATCH: {CHECKS_RUN} checks ran, {expected} expected. "
              f"Refusing to emit any verdict.")
        return 2
    if PRECOND_FAILED:
        print(f"NOT TESTED ({len(PRECOND_FAILED)}) — carries no evidence either way:")
        for f in PRECOND_FAILED:
            print("  ~", f)
    if CHECKS_FAILED:
        print(f"VERDICT: FAIL ({len(CHECKS_FAILED)})")
        for f in CHECKS_FAILED:
            print("  -", f)
        return 1
    if PRECOND_FAILED:
        print("VERDICT: INCONCLUSIVE — a gate never ran; it licenses nothing.")
        return 3
    print(f"VERDICT: PASS — {CHECKS_RUN}/{expected} checks, both predictions met")
    return 0


if __name__ == "__main__":
    sys.exit(selftest() if "--selftest" in sys.argv else main())
