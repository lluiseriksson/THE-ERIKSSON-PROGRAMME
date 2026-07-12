# C4 J-C4-4 certified grid: the Amos-type bound at REAL order.
# Protocol: docs/C4-CHARTER.md Amendment 6 (registered BEFORE this run).
# Margin Delta(nu,x) = B_nu(x) - rho_nu(x) certified by backward arb
# recurrence anchored at high order; PASS iff the ball is provably
# positive (never a midpoint verdict); precision ladder 128..4096;
# pi as a certified arb ball; independent mpmath pass labeled
# VERIFIED (not certified).
import hashlib
import sys

import flint
from flint import arb, ctx

SCRIPT_PATH = r"C:\Users\lluis\AppData\Local\Temp\eriksson-push2\scripts\c4_amos_real_arb.py"
PREC_LADDER = [128, 256, 512, 1024, 2048, 4096]


def provenance():
    h = hashlib.sha256(open(SCRIPT_PATH, "rb").read()).hexdigest().upper()
    print("== C4 REAL-ORDER AMOS GRID, CERTIFIED (arb) ==")
    print(f"script sha256 : {h}")
    print(f"python        : {sys.version.split()[0]}")
    print(f"python-flint  : {flint.__version__}")
    print("protocol      : charter Amendment 6 (registered pre-run)")
    print("grid          : 10 nu x 7 x = 70 points (Amendment 1)")
    print("ladder        : " + ", ".join(str(p) for p in PREC_LADDER) + " bits")
    print()


def nu_values():
    # exact/certified representations only; pi as arb ball at current prec
    return [
        ("0", arb(0)), ("1/10", arb(1) / 10), ("1/2", arb(1) / 2),
        ("9/10", arb(9) / 10), ("1", arb(1)), ("3/2", arb(3) / 2),
        ("2", arb(2)), ("pi", arb.pi()), ("10", arb(10)),
        ("100", arb(100)),
    ]


X_VALUES = [("1/8", (1, 8)), ("1/4", (1, 4)), ("1", (1, 1)),
            ("2", (2, 1)), ("5", (5, 1)), ("50", (50, 1)),
            ("300", (300, 1))]


def depth_N(nu_f, x_f):
    # minimal N with (x/2)^2/(nu+N+1) <= 1/4  i.e.  nu+N+1 >= x^2
    n = int(x_f * x_f - nu_f) + 2
    return max(n, 4)


def certify_point(nu, x, N):
    """Return (delta_ball, verdict) at current ctx.prec."""
    # anchor at alpha = nu + N: two-sided seed from the 3b-style bounds
    alpha = nu + N
    q_a = (x / 2) ** 2 / (alpha + 1)
    q_a1 = (x / 2) ** 2 / (alpha + 2)
    base = x / (2 * (alpha + 1))
    lo = base * (1 - q_a)
    hi = base / (1 - q_a1)
    rho = lo.union(hi)
    # backward: rho_{a} = x / (2(a+1) + x rho_{a+1}), a = nu+N-1 .. nu
    for j in range(N - 1, -1, -1):
        a = nu + j
        rho = x / (2 * (a + 1) + x * rho)
    # Amos-type RHS
    half = arb(1) / 2
    B = x / (nu + half + ((nu + half) ** 2 + x ** 2).sqrt())
    delta = B - rho
    if delta > 0:
        return delta, "PASS"
    if delta < 0:
        return delta, "FAIL"
    return delta, "UNDECIDED"


def main():
    provenance()
    rows = []
    counts = {"PASS": 0, "FAIL": 0, "UNDECIDED": 0}
    print(f"{'nu':>6} {'x':>5} {'N':>6} {'prec':>5} "
          f"{'Delta (mid +/- rad)':>42} verdict")
    for xs, (xp, xq) in X_VALUES:
        for prec0 in [PREC_LADDER[0]]:
            pass
        for nus_idx in range(10):
            verdict = "UNDECIDED"
            delta = None
            used_prec = None
            N = None
            for prec in PREC_LADDER:
                ctx.prec = prec
                nus, nu = nu_values()[nus_idx]
                x = arb(xp) / xq
                nu_f = float(nu.mid()) if nus != "pi" else 3.1416
                N = depth_N(nu_f, xp / xq)
                delta, verdict = certify_point(nu, x, N)
                used_prec = prec
                if verdict != "UNDECIDED":
                    break
            counts[verdict] += 1
            dstr = delta.str(12, radius=True)
            print(f"{nus:>6} {xs:>5} {N:>6} {used_prec:>5} {dstr:>42} "
                  f"{verdict}  [ball>0: {verdict == 'PASS'}]")
            rows.append((nus, xs, verdict))
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
    print(f"mpmath        : {mp.__version__}, dps = 50")
    mp.mp.dps = 50
    agree = 0
    total = 0
    for xs, (xp, xq) in X_VALUES:
        for nus, _ in [(s, None) for s, _ in
                       [("0", 0), ("1/10", 0), ("1/2", 0), ("9/10", 0),
                        ("1", 0), ("3/2", 0), ("2", 0), ("pi", 0),
                        ("10", 0), ("100", 0)]]:
            nu_mp = {"0": mp.mpf(0), "1/10": mp.mpf(1) / 10,
                     "1/2": mp.mpf(1) / 2, "9/10": mp.mpf(9) / 10,
                     "1": mp.mpf(1), "3/2": mp.mpf(3) / 2,
                     "2": mp.mpf(2), "pi": mp.pi, "10": mp.mpf(10),
                     "100": mp.mpf(100)}[nus]
            x_mp = mp.mpf(xp) / xq
            rho = mp.besseli(nu_mp + 1, x_mp) / mp.besseli(nu_mp, x_mp)
            B = x_mp / (nu_mp + mp.mpf(1) / 2
                        + mp.sqrt((nu_mp + mp.mpf(1) / 2) ** 2 + x_mp ** 2))
            d = B - rho
            total += 1
            if d > 0:
                agree += 1
            else:
                print(f"  DISAGREEMENT at nu={nus}, x={xs}: Delta = {d}")
    print(f"verified sign agreement: {agree}/{total} positive margins")
    print("== END ==")


if __name__ == "__main__":
    main()
