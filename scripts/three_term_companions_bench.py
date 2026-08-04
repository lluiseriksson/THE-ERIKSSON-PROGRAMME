"""Reception repair R3 bench: the THREE-TERM companions (the house
method one more order) and the witnessed variation constants for
(iv)(a)/(c) of lem:extraction. Derived claims under test:

  I_1 = e^z/sqrt(2 pi z) (1 - 3/(8z) - 15/(128 z^2) + eps1_3),
        |eps1_3| <= 1.02/z^3   (R_3 <= 3.54 u^6 Lagrange +
                                exact -45/(256 z^3) term + tails)
  I_0 = e^z/sqrt(2 pi z) (1 + 1/(8z) + 9/(128 z^2) + eps0_3),
        |eps0_3| <= 0.84/z^3
  eta(z) = r(z) - 1/z + 3/(2z^2) = 3/(8 z^3) + eta_4,
        |eta_4| <= 2.5/z^4
  variation witnesses (z_s >= 20, z = z_s sqrt(1-w), w <= 1/2):
    |eps_1(z) - eps_1(z_s)| <= 4.94/z_s^3 + 0.34 w/z_s^2
    |Delta eta|             <= 1.37 w/z_s^3 + 12.5/z_s^4
All checked against exact Bessel values on the machine range.
"""
import mpmath as mp

mp.mp.dps = 40
ok = True
print("=== three-term companions vs exact (z in [20, 112]) ===")
for zv in [20, 25, 30, 40, 60, 90, 112]:
    z = mp.mpf(zv)
    pref = mp.e**z/mp.sqrt(2*mp.pi*z)
    e1_3 = mp.besseli(1, z)/pref - (1 - 3/(8*z) - 15/(128*z**2))
    e0_3 = mp.besseli(0, z)/pref - (1 + 1/(8*z) + 9/(128*z**2))
    r = mp.besseli(2, z)/(z*mp.besseli(1, z))
    eta4 = (r - 1/z + 3/(2*z**2)) - 3/(8*z**3)
    print("  z=%4d : |e1_3| z^3 = %.4f (<=1.02)  |e0_3| z^3 = %.4f "
          "(<=0.84)  |eta_4| z^4 = %.4f (<=2.5)"
          % (zv, abs(e1_3)*z**3, abs(e0_3)*z**3, abs(eta4)*z**4))
    ok = ok and abs(e1_3)*z**3 <= mp.mpf("1.02") \
        and abs(e0_3)*z**3 <= mp.mpf("0.84") \
        and abs(eta4)*z**4 <= mp.mpf("2.5")
assert ok, "three-term companion bounds FAIL"
print("three-term bounds hold on the range.")

print("=== variation witnesses (z_s in {20, 48, 59.4}, w <= 1/2) ===")
for zsv in ["20", "48", "59.4"]:
    zs = mp.mpf(zsv)
    for wv in ["0.02", "0.1", "0.25", "0.5"]:
        w = mp.mpf(wv)
        z = zs*mp.sqrt(1 - w)
        pref = lambda x: mp.e**x/mp.sqrt(2*mp.pi*x)
        e1 = lambda x: mp.besseli(1, x)/pref(x) - (1 - 3/(8*x))
        de1 = abs(e1(z) - e1(zs))
        b1 = mp.mpf("4.94")/zs**3 + mp.mpf("0.34")*w/zs**2
        rr = lambda x: mp.besseli(2, x)/(x*mp.besseli(1, x))
        eta = lambda x: rr(x) - 1/x + 3/(2*x**2)
        deta = abs(eta(z) - eta(zs))
        b2 = mp.mpf("1.37")*w/zs**3 + mp.mpf("12.5")/zs**4
        okrow = de1 <= b1 and deta <= b2
        print("  z_s=%5s w=%.2f : |d eps1| = %.3e <= %.3e %s ; "
              "|d eta| = %.3e <= %.3e %s"
              % (zsv, float(w), de1, b1, de1 <= b1, deta, b2,
                 deta <= b2))
        ok = ok and okrow
assert ok, "variation witness FAILS"
print("=== Theta_3 and R_1 band with witnessed constants ===")
T = lambda c: (4*c**2 - 1)/(8*c**3)
r2 = lambda c: (-8*c**4 + 15*c**2 - 4)/(32*c**6)
r3 = lambda c: (-12*c**6 - 485*c**4 + 796*c**2 - 224)/(1024*c**9)
res = {mp.mpf("0.99"): (mp.mpf("0.101"), 3*mp.mpf("0.101")),
       mp.mpf("0.93"): (mp.mpf("0.1444"), 3*mp.mpf("0.1444")),
       mp.mpf("0.87"): (mp.mpf("0.1996"), 3*mp.mpf("0.1996")),
       mp.mpf("0.81"): (mp.mpf("0.292"), 3*mp.mpf("0.292"))}
allin = True
for cv, (lo, hi) in res.items():
    th = abs(r3(cv)) + mp.mpf("1.10")*T(cv)/cv**2 \
        + mp.mpf("0.5")/cv**3 + mp.mpf("0.05")
    R1 = abs(r2(cv)) + th/15
    inband = lo <= R1 <= hi
    print("  c = %.2f : Theta_3 = %.3f  R_1 = %.3f  band [%.3f, %.3f] "
          "in: %s" % (float(cv), float(th), float(R1), float(lo),
                      float(hi), inband))
    allin = allin and inband
assert allin, "R_1 band FAILS with witnessed constants"
print("THREE-TERM BENCH: ALL CHECKS PASS")
