# C5 J-C5-4 certified companion: THE CROSSING, independently.
# Protocol: docs/C5-CHARTER.md Amendment 8 + its technical note,
# both registered in OWN COMMITS (f6ec64ea, fdb0fe60) BEFORE this
# script existed and before any result was observed.
#
# INDEPENDENCE: the verdict logic below uses ONLY ball signs of
#   D(x)  = rho_nu(x) - B_{nu,c}(x)     and
#   D'(x) = 1 - ((2nu+1)/x) rho - rho^2 - a/(s(a+s))
# computed in arb ball arithmetic.  It NEVER consults
# amosFamily_global_crossing, amosFamily_crossing_orientation or
# crossing_scale.  The only in-tree theorems used are substrate:
# besselIReal_ratio_recurrence (the recurrence itself),
# besselIReal_pos and amosBoundReal_holds (the [0,1] seed), all
# from the RELEASED C4 lane.
#
# Per-pair certificates (Amendment 8):
#   1. BOX: certified opposite signs at the ends of X = [lo, hi],
#      found by certified bisection from the FIXED search interval
#      L0 = (1-c)/4, U0 = 8(nu+2)^2/(2c-1) (wider than the Lean
#      window BY RULE; the window is checked AFTER, never searched).
#   2. TRANSVERSALITY: inf_{x in X} D'(x) > 0 over the hull ball.
#   3. WINDOW: X inside [x_dagger, x_plus].
#   4. SCALE: 2a sqrt(c(1-c)) <= (2c-1) lo  and
#             (2c-1) hi <= 2((nu+3/2)^2 - a^2).
# PASS iff all four are ball-certified; UNDECIDED escalates the
# precision ladder ONLY; a CERTIFIED wrong endpoint sign is FAIL.
import hashlib
import math
import sys
from pathlib import Path

import flint
from flint import arb, ctx

SCRIPT_PATH = Path(__file__).resolve()
PREC_LADDER = [128, 256, 512, 1024, 2048, 4096]
BISECT_CAP = 200
REL_STOP_BITS = 60

NU_SPECS = ["0", "1/2", "1", "pi", "10", "100"]
C_SPECS = [("0.501", 501, 1000), ("0.6", 3, 5), ("0.75", 3, 4),
           ("0.9", 9, 10), ("0.999", 999, 1000)]


def provenance():
    h = hashlib.sha256(SCRIPT_PATH.read_bytes()).hexdigest().upper()
    print("== C5 CROSSING COMPANION, CERTIFIED (arb) ==")
    print(f"script sha256 : {h}")
    print(f"python        : {sys.version.split()[0]}")
    print(f"python-flint  : {flint.__version__}")
    print("protocol      : C5 charter Amendment 8 (f6ec64ea) + "
          "technical note (fdb0fe60), both PRE-RUN")
    print("grid          : 6 nu x 5 c = 30 pairs (hard regimes forced)")
    print("ladder        : " + ", ".join(str(p) for p in PREC_LADDER)
          + " bits")
    print("independence  : verdicts by ball signs of D, D' ONLY; the")
    print("                three crossing theorems are NEVER consulted")
    print()


def make_nu(tag):
    # exact/certified representations only; pi as arb ball at ctx.prec
    return {"0": arb(0), "1/2": arb(1) / 2, "1": arb(1),
            "pi": arb.pi(), "10": arb(10), "100": arb(100)}[tag]


def x_sup_float(x):
    return float(x.mid()) + float(x.rad())


def depth_N(x, prec):
    # technical note items 1+4: N = ceil(2*sqrt(max(x,1)*prec)) + 40;
    # contraction certified a posteriori by the final ball width
    # (too-wide balls can only yield UNDECIDED, never a wrong verdict)
    return int(math.ceil(
        2 * math.sqrt(max(x_sup_float(x), 1.0) * prec))) + 40


def rho_ball(nu, x, prec):
    """Certified enclosure of rho_nu(x) = I_{nu+1}/I_nu at ctx.prec.

    Seed: rho_{nu+N}(x) in [0, 1] (besselIReal_pos +
    amosBoundReal_holds).  Backward: rho_a = x/(2(a+1) + x rho_{a+1})
    (besselIReal_ratio_recurrence), pure ball arithmetic."""
    N = depth_N(x, prec)
    rho = arb(0).union(arb(1))
    for j in range(N - 1, -1, -1):
        a = nu + j
        rho = x / (2 * (a + 1) + x * rho)
    return rho, N


def D_ball(nu, c, x, prec):
    a = nu + c
    s = (a * a + x * x).sqrt()
    B = x / (a + s)
    rho, N = rho_ball(nu, x, prec)
    return rho - B, N


def Dprime_ball(nu, c, x, prec):
    a = nu + c
    s = (a * a + x * x).sqrt()
    rho, N = rho_ball(nu, x, prec)
    rp = 1 - ((2 * nu + 1) / x) * rho - rho * rho
    Bp = a / (s * (a + s))
    return rp - Bp, N


def certify_pair(nu, c, prec):
    """One (nu, c) pair at one ladder rung.  Returns a record dict."""
    ctx.prec = prec
    L0 = (1 - c) / 4
    U0 = 8 * (nu + 2) ** 2 / (2 * c - 1)
    rec = {"prec": prec, "Nmax": 0, "steps": 0, "stop": "", "fail": False}
    dL, N1 = D_ball(nu, c, L0, prec)
    dU, N2 = D_ball(nu, c, U0, prec)
    rec["Nmax"] = max(N1, N2)
    rec["dL"], rec["dU"] = dL, dU
    if dL > 0 or dU < 0:
        rec["fail"] = True  # certified wrong sign: full stop + autopsy
        return rec
    if not (dL < 0 and dU > 0):
        return rec  # straddle at an endpoint: UNDECIDED, escalate
    lo, hi, dlo, dhi = L0, U0, dL, dU
    eps = arb(1) / arb(2) ** REL_STOP_BITS
    while rec["steps"] < BISECT_CAP:
        if (hi - lo) < hi * eps:
            rec["stop"] = "relwidth<=2^-60"
            break
        mid = (lo + hi) / 2
        d, N = D_ball(nu, c, mid, prec)
        rec["Nmax"] = max(rec["Nmax"], N)
        rec["steps"] += 1
        if d < 0:
            lo, dlo = mid, d
        elif d > 0:
            hi, dhi = mid, d
        else:
            rec["stop"] = "midpoint-straddle"
            break
    else:
        rec["stop"] = "cap200"
    # ---- the four certificates, all ball-certified ----
    a = nu + c
    hull = lo.union(hi)
    dp, N3 = Dprime_ball(nu, c, hull, prec)
    rec["Nmax"] = max(rec["Nmax"], N3)
    x_dag = 2 * a * (c * (1 - c)).sqrt() / (2 * c - 1)
    x_plus = 2 * ((nu + arb(3) / 2) ** 2 - a * a) / (2 * c - 1)
    scale_lhs = 2 * a * (c * (1 - c)).sqrt()
    scale_rhs = 2 * ((nu + arb(3) / 2) ** 2 - a * a)
    rec.update(
        lo=lo, hi=hi, dlo=dlo, dhi=dhi, dp=dp,
        x_dag=x_dag, x_plus=x_plus,
        c_box=bool(dlo < 0) and bool(dhi > 0),
        c_transv=bool(dp > 0),
        c_window=bool(x_dag < lo) and bool(hi < x_plus),
        c_scale=(bool(scale_lhs <= (2 * c - 1) * lo)
                 and bool((2 * c - 1) * hi <= scale_rhs)),
    )
    return rec


def main():
    provenance()
    results = []
    counts = {"PASS": 0, "FAIL": 0, "UNDECIDED": 0}
    for nu_tag in NU_SPECS:
        for c_tag, cp, cq in C_SPECS:
            verdict, rec = "UNDECIDED", None
            for prec in PREC_LADDER:
                ctx.prec = prec
                nu = make_nu(nu_tag)
                c = arb(cp) / cq
                rec = certify_pair(nu, c, prec)
                if rec["fail"]:
                    verdict = "FAIL"
                    break
                if all(rec.get(k, False) for k in
                       ("c_box", "c_transv", "c_window", "c_scale")):
                    verdict = "PASS"
                    break
            counts[verdict] += 1
            print(f"nu={nu_tag:>4} c={c_tag:<5} prec={rec['prec']:>5} "
                  f"Nmax={rec['Nmax']:>7} steps={rec['steps']:>3} "
                  f"stop={rec['stop'] or '-'}")
            if "lo" in rec:
                w = rec["hi"] - rec["lo"]
                print(f"   X = [{rec['lo'].str(25)}, {rec['hi'].str(25)}]"
                      f"  width={w.str(6)}")
                print(f"   D(lo)={rec['dlo'].str(8)}  "
                      f"D(hi)={rec['dhi'].str(8)}  "
                      f"[box: {rec['c_box']}]")
                print(f"   D'(X)={rec['dp'].str(8, radius=True)}  "
                      f"[transversal: {rec['c_transv']}]")
                print(f"   x_dag={rec['x_dag'].str(12)}  "
                      f"x_plus={rec['x_plus'].str(12)}  "
                      f"[window: {rec['c_window']}] "
                      f"[scale: {rec['c_scale']}]")
            else:
                print(f"   endpoint balls: D(L0)={rec['dL'].str(8)} "
                      f"D(U0)={rec['dU'].str(8)}")
            print(f"   VERDICT: {verdict}")
            results.append((nu_tag, c_tag, verdict, rec))
    print()
    print(f"SUMMARY certified: PASS {counts['PASS']} / "
          f"FAIL {counts['FAIL']} / UNDECIDED {counts['UNDECIDED']} "
          f"of {sum(counts.values())}")
    if counts["FAIL"] or counts["UNDECIDED"]:
        print("!! NON-PASS ROWS PRESENT - full stop + autopsy per charter")
    # -------- independent ordinary pass: VERIFIED, NOT certified ----
    print()
    print("== INDEPENDENT CROSS-CHECK (mpmath, VERIFIED - NOT certified) ==")
    import mpmath as mp
    print(f"mpmath        : {mp.__version__}, dps = 60")
    mp.mp.dps = 60
    agree = 0
    total = 0
    for nu_tag, c_tag, verdict, rec in results:
        if "lo" not in rec:
            continue
        total += 1
        nu_mp = {"0": mp.mpf(0), "1/2": mp.mpf(1) / 2, "1": mp.mpf(1),
                 "pi": mp.pi, "10": mp.mpf(10), "100": mp.mpf(100)}[nu_tag]
        cp, cq = {"0.501": (501, 1000), "0.6": (3, 5), "0.75": (3, 4),
                  "0.9": (9, 10), "0.999": (999, 1000)}[c_tag]
        c_mp = mp.mpf(cp) / cq
        a_mp = nu_mp + c_mp

        def D_mp(x):
            r = mp.besseli(nu_mp + 1, x) / mp.besseli(nu_mp, x)
            return r - x / (a_mp + mp.sqrt(a_mp ** 2 + x ** 2))

        lo_mp = mp.mpf(rec["lo"].mid().str(40, radius=False))
        hi_mp = mp.mpf(rec["hi"].mid().str(40, radius=False))
        mid_mp = (lo_mp + hi_mp) / 2
        h = max(mid_mp * mp.mpf("1e-20"), mp.mpf("1e-30"))
        dprime = (D_mp(mid_mp + h) - D_mp(mid_mp - h)) / (2 * h)
        ok = D_mp(lo_mp) < 0 < D_mp(hi_mp) and dprime > 0
        if ok:
            agree += 1
        else:
            print(f"  DISAGREEMENT at nu={nu_tag}, c={c_tag}")
    print(f"verified agreement (signs at box ends + D' > 0 at mid): "
          f"{agree}/{total}")
    print("== END ==")


if __name__ == "__main__":
    main()
