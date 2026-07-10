"""Unit tests for safe_sqrt's contract (ghost #22 repair, audit round
2026-07-10s). Cases mandated by the external desk: [-ulp, 1], [0, 0],
tiny intervals, truly negative input. Plus the original killer: the
full-domain R^2 ball whose reconstruction dips one ulp below zero.

Pass criterion for each case: result is FINITE and CONTAINS the true
range [sqrt(max(0,lo)), sqrt(max(0,hi))]."""
from flint import arb, ctx
import exp_integrator_arb as m

ctx.prec = 90
fails = 0


def check(name, x, true_lo, true_hi):
    global fails
    out = m.safe_sqrt(x)
    lo = float(m.ball_lo(out)); hi = float(m.ball_hi(out))
    finite = out.is_finite()
    contains = (lo <= true_lo + 1e-15) and (hi >= true_hi - 1e-15)
    ok = finite and contains
    if not ok:
        fails += 1
    print("%-28s -> [%.6g, %.6g] finite=%s contains=%s %s"
          % (name, lo, hi, finite, contains, "OK" if ok else "FAIL"),
          flush=True)


# 1. [-ulp, 1]: the ghost-#22 shape - reconstruction slack below zero
x = (arb(1)/2) + (arb(1)/2)*arb("0 +/- 1")   # ~[−ulp, 1+ulp]
check("[-ulp, 1] (ghost shape)", x, 0.0, 1.0)

# 2. [0, 0]: exact zero ball
check("[0, 0]", arb(0), 0.0, 0.0)

# 3. tiny interval around a tiny positive value
t = arb(1)/arb(10)**30
x = t + (t/2)*arb("0 +/- 1")
check("tiny positive interval", x, (0.5e-30)**0.5, (1.5e-30)**0.5)

# 4. tiny interval straddling zero
x = arb("0 +/- 1e-30")
check("tiny straddling zero", x, 0.0, 1e-15)

# 5. truly negative input (contract: only true squares may arrive here,
#    so a fully negative ball must clamp to [0,0], not NaN)
check("truly negative [-2,-1]", arb("-1.5 +/- 0.5"), 0.0, 0.0)

# 6. the original killer: full-domain R^2 at (t,b) = (1.5, 8)
pt = m.V2((15, 10), (8, 1), prec=90)
X = m.hull(arb(0), arb(1)); Y = m.hull(arb(0), arb(1))
S, A, P, Q, R2, z = pt.geom(X, Y)
ok6 = z.is_finite() and (arb(0) <= m.ball_hi(z))
if not ok6:
    fails += 1
print("%-28s -> z=[%.6g, %.6g] finite=%s %s"
      % ("full-domain R^2 (killer)", float(m.ball_lo(z)),
         float(m.ball_hi(z)), z.is_finite(), "OK" if ok6 else "FAIL"),
      flush=True)

print("RESULT:", "ALL OK" if fails == 0 else "%d FAILURES" % fails,
      flush=True)
raise SystemExit(0 if fails == 0 else 1)
