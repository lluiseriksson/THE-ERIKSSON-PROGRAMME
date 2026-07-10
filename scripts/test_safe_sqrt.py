"""Unit tests for safe_sqrt's contract v2 (audit round 2026-07-10t).
Cases: [-ulp,1] ghost shape, [0,0], tiny intervals, straddling zero,
truly negative input (MUST RAISE), and the original full-domain killer.

Containment is checked IN ARB BALLS, not via float tolerances: for a
true range [a, b] (a, b given as exact rationals or arb expressions)
we require ball_lo(out) <= a and b <= ball_hi(out) as arb comparisons.
Pass criterion: result finite and containing; negative input raises."""
from flint import arb, ctx
import exp_integrator_arb as m

ctx.prec = 90
fails = 0


def check(name, x, true_lo, true_hi):
    """true_lo/true_hi: arb balls enclosing the true range endpoints."""
    global fails
    out = m.safe_sqrt(x)
    lo = m.ball_lo(out); hi = m.ball_hi(out)
    finite = bool(out.is_finite())
    # arb comparisons: lo <= true_lo requires the WHOLE lo ball to sit
    # at or below the whole true_lo ball - strict, no float tolerance
    contains = bool(lo <= true_lo) and bool(true_hi <= hi)
    ok = finite and contains
    if not ok:
        fails += 1
    print("%-28s -> [%s, %s] finite=%s contains=%s %s"
          % (name, lo.str(6), hi.str(6), finite, contains,
             "OK" if ok else "FAIL"), flush=True)


# 1. [-ulp, 1]: the ghost-#22 shape - reconstruction slack below zero.
#    True range of sqrt over [0, 1+ulp]: [0, ~1].
x = (arb(1)/2) + (arb(1)/2)*arb("0 +/- 1")
check("[-ulp, 1] (ghost shape)", x, arb(0), arb(1))

# 2. [0, 0]: exact zero ball
check("[0, 0]", arb(0), arb(0), arb(0))

# 3. tiny interval around a tiny positive value: x in [t/2, 3t/2],
#    t = 10^-30; true sqrt range endpoints as arb sqrt of exact points
t = arb(1)/arb(10)**30
x = t + (t/2)*arb("0 +/- 1")
check("tiny positive interval", x, (t/2).sqrt(), (3*t/2).sqrt())

# 4. tiny interval straddling zero: true range [0, sqrt(1e-30)]
x = arb("0 +/- 1e-30")
check("tiny straddling zero", x, arb(0), arb("1e-30").sqrt())

# 4b. UPPER end straddling zero (the case formerly served by the ad-hoc
#     dyadic branch, now by abs_upper): x = [-2e-40, 0]; true range of
#     sqrt over max(0, x) is [0, 0]; abs_upper gives a conservative
#     but rigorous upper bound (~1.4e-20)
x = arb("-1e-40 +/- 1e-40")
check("upper straddling zero", x, arb(0), arb(0))

# 5. truly negative input MUST RAISE (contract violation, never masked)
try:
    m.safe_sqrt(arb("-1.5 +/- 0.5"))
    fails += 1
    print("%-28s -> NO EXCEPTION FAIL" % "truly negative [-2,-1]",
          flush=True)
except ValueError as e:
    print("%-28s -> ValueError OK (%s...)"
          % ("truly negative [-2,-1]", str(e)[:42]), flush=True)

# 6. the original killer: full-domain R^2 at (t,b) = (1.5, 8)
pt = m.V2((15, 10), (8, 1), prec=90)
X = m.hull(arb(0), arb(1)); Y = m.hull(arb(0), arb(1))
S, A, P, Q, R2, z = pt.geom(X, Y)
ok6 = bool(z.is_finite()) and bool(arb(0) <= m.ball_hi(z))
if not ok6:
    fails += 1
print("%-28s -> z=[%s, %s] finite=%s %s"
      % ("full-domain R^2 (killer)", m.ball_lo(z).str(6),
         m.ball_hi(z).str(6), bool(z.is_finite()),
         "OK" if ok6 else "FAIL"), flush=True)

print("RESULT:", "ALL OK" if fails == 0 else "%d FAILURES" % fails,
      flush=True)
raise SystemExit(0 if fails == 0 else 1)
