"""C2 COMPANION - CERTIFIED pointwise verification of the Amos bound
on the pre-registered consumer grid (charter docs/C2-CHARTER.md,
judge J-C2-2; python-flint arb, prec 256 bits).

THE OBJECT: for integer nu >= 0 and x > 0,
    ratio(nu, x) = I_{nu+1}(x) / I_nu(x)
    amosRHS(nu, x) = x / (nu + 1/2 + sqrt((nu+1/2)^2 + x^2))
CLAIM CERTIFIED POINTWISE (strict): ratio < amosRHS.

ENCLOSURE METHOD (self-contained; no library Bessel):
  I_n(x) = sum_{k>=0} (x/2)^{n+2k} / (k! (n+k)!)
  truncated at K = max(40, ceil(0.75 x) + 40) terms, with the
  certified geometric tail: for k >= K the term ratio is
  <= q = (x/2)^2/((K+1)(n+K+1)) (checked provably < 1/2 per point),
  so tail <= t_K * q/(1-q) <= t_K; the tail is added as the interval
  [0, t_K * q/(1-q)] (outward).  All grid x are dyadic (exact in
  binary), so series arithmetic starts from exact inputs.

PRE-REGISTERED GRID (consumer-driven, charter):
  bulk: nu in {0..20} x x in {0.25, 0.50, ..., 14.00}   (1176 pts)
  wide: nu in {0..5}  x x in {20, 50, 100, 200, 300}    (  30 pts)

JUDGES (registered): (J1) EVERY point PASS provably (tri-state:
PASS only if ratio < rhs for all ball points; FAIL only if rhs <=
ratio provably; else UNDECIDED - any non-PASS = judge fails).
(J2) the slack min is MEASURED (ball lower bound) and reported with
a diagnostic-only comparison against the twin desk's exact2d figure
(2.5e-7 on [1,100]x[0.01,300], repo recon) - explicitly NOT a
registered prediction of this desk (C1 crossover lesson).

Every printed enclosure carries ball + boolean (regime pt 7).
"""
import hashlib
import sys

from flint import arb, ctx

ctx.prec = 256

def blo(z):
    return arb(z.mid()) - arb(z.rad())

def bhi(z):
    return arb(z.mid()) + arb(z.rad())

print("=== C2 COMPANION: certified Amos-bound grid (arb) ===")
print("script sha256 : %s"
      % hashlib.sha256(open(__file__, "rb").read()).hexdigest())
try:
    import flint
    fv = getattr(flint, "__version__", "unknown")
except Exception:
    fv = "unknown"
print("python-flint %s  python %s  prec %d bits"
      % (fv, sys.version.split()[0], ctx.prec), flush=True)

HALF = arb(1)/2
UNIT = arb("0.5 +/- 0.5")     # the interval [0, 1]

def bessel_I_pair(n, x):
    """Certified enclosures of (I_n(x), I_{n+1}(x)) for integer
    n >= 0, dyadic x > 0.  Returns (In, In1, ok) with ok = True iff
    both tail ratios were provably < 1/2."""
    xh = x / 2
    xh2 = xh * xh
    ok = True
    out = []
    for m in (n, n + 1):
        K = max(40, int(float(x)) * 3 // 4 + 41)
        # t_0 = (x/2)^m / m!
        t = xh ** m
        for j in range(1, m + 1):
            t = t / j
        s = arb(0)
        for k in range(K):
            s = s + t
            t = t * xh2 / ((k + 1) * (m + k + 1))
        # t now = t_K; tail ratio bound q at k = K
        q = xh2 / ((K + 1) * (m + K + 1))
        if not bool(q < HALF):
            ok = False
        tail_hi = t * q / (1 - q)
        s = s + tail_hi * UNIT
        out.append(s)
    return out[0], out[1], ok

def check_point(n, x):
    """Returns (verdict, slack) at integer order n, dyadic x."""
    In, In1, ok = bessel_I_pair(n, x)
    if not ok:
        return "TAILFAIL", None
    ratio = In1 / In
    a = arb(n) + HALF
    rhs = x / (a + (a * a + x * x).sqrt())
    if bool(ratio < rhs):
        verdict = "PASS"
    elif bool(rhs <= ratio):
        verdict = "FAIL"
    else:
        verdict = "UNDECIDED"
    return verdict, rhs - ratio

BULK_NU = range(0, 21)
BULK_X = [arb(k) / 4 for k in range(1, 57)]          # 0.25 .. 14.00
WIDE_NU = range(0, 6)
WIDE_X = [arb(20), arb(50), arb(100), arb(200), arb(300)]

npass = nfail = nund = 0
min_slack_lo = None
min_at = None

print("\n--- bulk grid: nu in 0..20, x = 0.25(0.25)14.00 ---")
print("  (per point: verdict, slack ball; full rows for every point)")
for n in BULK_NU:
    row = []
    for x in BULK_X:
        v, slack = check_point(n, x)
        if v == "PASS":
            npass += 1
        elif v == "FAIL":
            nfail += 1
        else:
            nund += 1
        lo = blo(slack)
        if (min_slack_lo is None) or bool(lo < min_slack_lo):
            min_slack_lo = lo
            min_at = (n, x)
        row.append("x=%s %s slack[%s,%s]"
                   % (str(float(x)), v, lo.str(5), bhi(slack).str(5)))
    print("nu=%2d | %s" % (n, " ; ".join(row)), flush=True)

print("\n--- wide columns: nu in 0..5, x in {20,50,100,200,300} ---")
for n in WIDE_NU:
    for x in WIDE_X:
        v, slack = check_point(n, x)
        if v == "PASS":
            npass += 1
        elif v == "FAIL":
            nfail += 1
        else:
            nund += 1
        lo = blo(slack)
        if (min_slack_lo is None) or bool(lo < min_slack_lo):
            min_slack_lo = lo
            min_at = (n, x)
        print("  nu=%d x=%3d : %s  slack in [%s, %s]"
              % (n, int(float(x)), v, lo.str(8), bhi(slack).str(8)),
              flush=True)

print("\n--- JUDGES ---")
total = npass + nfail + nund
print("points: %d   PASS %d   FAIL %d   UNDECIDED %d"
      % (total, npass, nfail, nund))
print("J1 (all points provably strict): %s"
      % ("PASS" if (nfail == 0 and nund == 0 and total == 1206)
         else "FAIL"))
print("J2 (measured slack floor, ball lower bound): %s at nu=%d x=%s"
      % (min_slack_lo.str(10), min_at[0], str(float(min_at[1]))))
print("   diagnostic-only comparison: twin desk exact2d reported "
      "2.5e-7 on [1,100]x[0.01,300] (recon); NOT a registered "
      "prediction of this desk.", flush=True)
