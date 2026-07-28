"""Non-rigorous complex-circle probe for a beta Taylor remainder.

It evaluates the finite pair-regrouped Wronskian at sample points on a
complex beta circle.  A useful Cauchy route would require a rigorous angular
cover and tail bound; this script intentionally supplies neither and carries
no G2/G6 load.
"""

from fractions import Fraction
import cmath
import mpmath as mp

from flint import acb, arb, ctx


def beta_acb(z):
    return acb(arb(mp.nstr(mp.re(z), 180)), arb(mp.nstr(mp.im(z), 180)))


def scaled_j(n, beta):
    return (-beta).exp()*beta.bessel_i(n)


def eval_w(beta, t, M):
    J = {m: scaled_j(m, beta) for m in range(0, M + 3)}
    a = {}; b = {}
    for m in range(1, M + 2):
        a[m] = J[m]**2*((m-1)*J[m-1]**2+(m+1)*J[m+1]**2)
        b[m] = arb(m)*J[m]**4
    T = arb(mp.nstr(t, 180))
    total = acb(0)
    for m in range(1, M + 1):
        sm=(arb(m)*T).sin(); cm=(arb(m)*T).cos()
        for n in range(m+1, M+1):
            sn=(arb(n)*T).sin(); cn=(arb(n)*T).cos()
            K=arb(m)*cm*sn-arb(n)*sm*cn
            total += (a[m]*b[n]-a[n]*b[m])*K
    return 2*total


def eval_arc(beta_mid, radius, theta_mid, theta_radius, t, M):
    """Evaluate on a rectangular Arb enclosure containing one circle arc."""
    th = arb(mp.nstr(theta_mid, 180)) + arb(mp.nstr(theta_radius, 180)) * arb("0 +/- 1")
    real = arb(mp.nstr(beta_mid, 180)) + arb(mp.nstr(radius, 180))*th.cos()
    imag = arb(mp.nstr(radius, 180))*th.sin()
    return eval_w(acb(real, imag), t, M)


def main():
    ctx.prec = 500
    mp.mp.dps = 180
    beta_mid = mp.mpf(1629)/16 + mp.mpf(1)/32
    radius = mp.mpf("0.1")
    t = mp.mpf(1311)/500 + mp.mpf("0.0005")
    M = 160
    max_abs = mp.mpf(0)
    for k in range(64):
        z = beta_mid + radius*mp.e**(2j*mp.pi*k/64)
        w = eval_w(beta_acb(z), t, M)
        value = mp.mpf(float(w.abs_upper()))
        max_abs = max(max_abs, value)
        print("ANGLE", k, "ABS_UPPER", w.abs_upper().str(30), flush=True)
    print("CAUCHY_DIAGNOSTIC_ONLY")
    print("BETA_MID", beta_mid, "RADIUS", radius, "T", t, "M", M)
    print("MAX_ABS_UPPER", mp.nstr(max_abs, 30))
    arc_max = mp.mpf(0)
    for k in range(64):
        theta = 2*mp.pi*(k+mp.mpf("0.5"))/64
        w = eval_arc(beta_mid, radius, theta, mp.pi/64, t, M)
        value = mp.mpf(float(w.abs_upper()))
        arc_max = max(arc_max, value)
        print("ARC", k, "ABS_UPPER", w.abs_upper().str(30), flush=True)
    print("ARC_RECTANGLE_MAX_ABS_UPPER", mp.nstr(arc_max, 30))
    print("NO G2/G6 PROMOTION")


if __name__ == "__main__":
    main()
