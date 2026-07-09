"""CERTIFIED NEGATIVE - time-3 marginal of the killed 4-step bridge is NOT
stochastically monotone in its endpoint.

PROPOSITION (pinned statement, all normalizations explicit).
Work on (0, pi) with beta = 20. Kernel and entry law:
    q1(u,v) = 2 e^{beta cos u cos v} sinh(beta sin u sin v)
            = 4 sum_{m>=1} I_m(beta) sin(mu) sin(mv),
    s1(u)   = (beta/2) sin u e^{beta cos u} = sum_{m>=1} m I_m(beta) sin(mu),
    (Qf)(v) = (1/2pi) int_0^pi q1(v,u) f(u) du   (eigenvalues I_m(beta)).
The TIME-3 MARGINAL of the 4-step bridge entering from 0 with law s1 and
conditioned to end at t is
    rho_t(u) prop. (Q^2 s1)(u) * q1(u,t),
    (Q^2 s1)(u) = sum_{m>=1} m I_m(beta)^3 sin(mu).
CLAIM: with a = 4802/10^4, t1 = 29621/10^4, t2 = 30070/10^4:
    T(t2, a) < T(t1, a),   where   T(t, a) = int_a^pi rho_t / int_0^pi rho_t.
Hence the family {rho_t} is not stochastically increasing in t. One certified
witness suffices for the negative. Consequence: no monotone coupling of FULL
bridge paths can exist at beta = 20 (all time marginals of such a coupling
would be st-monotone). The time-2 (midpoint) marginal is NOT affected.

METHOD. Tails are EXACT double sums via the closed form
    J(m,n,a) = int_a^pi sin(mu) sin(nu) du
      = -[ sin((m-n)a)/(2(m-n)) - sin((m+n)a)/(2(m+n)) ]   (m != n)
      =  (pi-a)/2 + sin(2ma)/(4m)                          (m == n),
so there is NO quadrature error; the only error sources are (a) interval
rounding, (b) Bessel enclosures, (c) series truncation - all controlled below.

TRUST BASE (declared). Certified modulo the correctness of mpmath.iv's
outward-rounding interval arithmetic. Floating-point numbers appear ONLY in
loop-termination heuristics, never in the validity of any enclosure.
An independent Arb port (certify_time3_negative_arb.py, python-flint) runs
the same algorithm on a second interval implementation.

BESSEL ENCLOSURES. I_m(20) = sum_{j>=0} 10^{m+2j}/(j!(m+j)!), all terms
positive, so partial sums are rigorous lower bounds. Term ratio
    r_j = 100/((j+1)(m+j+1))
is decreasing in j; once (j+1)(m+j+1) >= 200 (exact integer test, r_j <= 1/2)
the tail is <= t_j * r_j/(1 - r_j), added as the interval [0, bound].

TRUNCATION BOUNDS (algebraic). With B_m := 10^m e^{100}/m! >= I_m(20)
(standard bound I_m(x) <= (x/2)^m e^{x^2/4}/m!):
  * sum_{n>M} I_n <= B_{M+1} / (1 - 10/(M+2))   [B_{m+1}/B_m = 10/(m+1)
    decreasing, so the B-tail is dominated by the geometric series of
    ratio 10/(M+2)]
  * sum_{m>M} m I_m^3 <= 2 (M+1) B_{M+1}^3      [consecutive-term ratio
    (m+1)B_{m+1}^3/(m B_m^3) = (10/(m+1))^3 (m+1)/m < 1/1000 for m >= 120,
    so the sum is < first term / (1 - 1/1000) < 2 * first term]
  * |J(m,n,a)| <= pi uniformly.
Every term dropped from the double sum contributes at most
    eps = 4 pi [ (sum_{m>M} m I_m^3)(sum_{n>=1} I_n)
               + (sum_{m<=M} m I_m^3)(sum_{n>M} I_n) ]
to numerator or denominator (the factor 4 pi majorizes 4|I_n sin| |J|);
eps is computed IN INTERVALS and added as [-eps, eps] to all four quantities.

SELF-VERIFICATION (nesting). The certificate is computed twice, at
(M, prec) = (120, 350) and (140, 500). The script ASSERTS that the second
enclosure is contained in the first and that both are strictly negative.
Nested enclosures prevent silent numerical or truncation degradation;
statement auditing and the independent Arb implementation guard against
common-mode errors.

Sign decision: T(t2,a) - T(t1,a) = (TN2*D1 - TN1*D2)/(D1*D2); we certify
D1 > 0, D2 > 0 and R := TN2*D1 - TN1*D2 < 0.
"""
from mpmath import iv
from math import factorial


def besseli_iv(m, X):
    """Enclosure of I_m(20): positive-term series + geometric tail (header)."""
    s = iv.mpf(0)
    j = 0
    while True:
        t = X ** (m + 2 * j) / (iv.mpf(factorial(j)) * iv.mpf(factorial(m + j)))
        s += t
        if (j + 1) * (m + j + 1) >= 200:  # exact integer test: ratio <= 1/2
            # float used ONLY to decide when to stop; the tail bound below
            # is added in intervals regardless
            if float(t.b) < 1e-120 * max(float(s.a), 1e-300):
                r = iv.mpf(100) / (iv.mpf(j + 1) * iv.mpf(m + j + 1))
                s += iv.mpf([0, 1]) * (t * r / (1 - r))
                return s
        j += 1


def certify(M, prec):
    iv.prec = prec
    X = iv.mpf(10)  # beta/2, exact
    I = [besseli_iv(m, X) for m in range(M + 1)]
    A = iv.mpf(4802) / iv.mpf(10000)
    T1 = iv.mpf(29621) / iv.mpf(10000)
    T2 = iv.mpf(30070) / iv.mpf(10000)
    PI = iv.pi
    sa = [iv.sin(iv.mpf(k) * A) for k in range(2 * M + 1)]
    sv1 = [iv.sin(iv.mpf(n) * T1) for n in range(M + 1)]
    sv2 = [iv.sin(iv.mpf(n) * T2) for n in range(M + 1)]

    def assemble(sv):
        TN = iv.mpf(0)
        D = iv.mpf(0)
        for m in range(1, M + 1):
            cm = iv.mpf(m) * I[m] ** 3
            row = iv.mpf(0)
            for n in range(1, M + 1):
                if m == n:
                    J = (PI - A) / 2 + sa[2 * m] / (iv.mpf(4) * iv.mpf(m))
                else:
                    # sin((m-n)a) = sgn(m-n) * sin(|m-n| a)
                    sgn = 1 if m > n else -1
                    J = -(iv.mpf(sgn) * sa[abs(m - n)] / (iv.mpf(2) * iv.mpf(m - n))
                          - sa[m + n] / (iv.mpf(2) * iv.mpf(m + n)))
                row += iv.mpf(4) * I[n] * sv[n] * J
            TN += cm * row
            D += cm * iv.mpf(4) * I[m] * sv[m] * (PI / 2)
        return TN, D

    # truncation error (header: TRUNCATION BOUNDS), computed in intervals
    E100 = iv.exp(iv.mpf(100))
    BM1 = X ** (M + 1) * E100 / iv.mpf(factorial(M + 1))
    tailI = BM1 / (1 - iv.mpf(10) / iv.mpf(M + 2))
    sumI = sum(I[n] for n in range(1, M + 1)) + tailI
    summ3 = sum(iv.mpf(m) * I[m] ** 3 for m in range(1, M + 1))
    tailm3 = iv.mpf(2) * iv.mpf(M + 1) * BM1 ** 3
    eps = iv.mpf(4) * PI * (tailm3 * sumI + summ3 * tailI)
    ERR = iv.mpf([-1, 1]) * eps

    TN1, D1 = assemble(sv1)
    TN2, D2 = assemble(sv2)
    TN1 += ERR; TN2 += ERR; D1 += ERR; D2 += ERR

    assert D1 > 0 and D2 > 0, "denominators not certified positive"
    R = TN2 * D1 - TN1 * D2
    diff = R / (D1 * D2)
    assert diff < 0, "difference not certified negative"
    return diff


if __name__ == "__main__":
    d1 = certify(M=120, prec=350)
    print("pass 1 (M=120, prec=350):", d1)
    d2 = certify(M=140, prec=500)
    print("pass 2 (M=140, prec=500):", d2)
    # nesting: the refined enclosure must lie inside the coarse one
    assert d1.a <= d2.a and d2.b <= d1.b, "NESTING FAILURE"
    print("NESTING OK: refined enclosure contained in coarse enclosure")
    print("CERTIFIED: T(t2,a) - T(t1,a) < 0  (both passes, nested)")
