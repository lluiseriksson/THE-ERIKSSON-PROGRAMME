EXTERNAL RE-DERIVATION COMMISSION - g_comp load-bearing links
(read-only; rederive independently; numbers only after your own
computation; do not edit files; do not read scripts/cascade3c*.py
before answering - derive from the statements alone)

Setting: POLY(sigma,tau,eps) is a polynomial where the variables
sigma, tau ONLY ever appear through the products (sigma*eps) and
(tau*eps) (it is built from Taylor polynomials of cos(sigma*eps),
cos(tau*eps) and products thereof, plus eps^2-weighted series).
Gaussian weight e^{-p(sigma^2+tau^2)/2}, p in [0.58, 0.82].
R = 1.2*sqrt(beta), eps = 1/sqrt(beta), beta >= 15.

Verify each claim (PASS/FAIL + one-line derivation each):

L1. Tail-moment recursion: for T_k(R) := int_R^inf x^k e^{-p x^2/2} dx,
    T_k(R) = R^{k-1} e^{-p R^2/2}/p + ((k-1)/p) T_{k-2}(R)  (k>=2),
    T_0(R) <= e^{-p R^2/2}/(p R),   T_1(R) = e^{-p R^2/2}/p.

L2. Strip union: the complement of the square [-R,R]^2 is contained
    in {|sigma|>R} union {|tau|>R}, so for any nonneg integrand
    int_{complement} <= int_{|sigma|>R, tau in RR} + int_{sigma in RR, |tau|>R}.

L3. Structural degree bound: if sigma and tau only appear as
    (sigma*eps), (tau*eps), then every monomial a*sigma^i*tau^j*eps^k
    of POLY has k >= i + j.

L4. beta-monotonicity: for a monomial contribution
    f(beta) = beta^{2 - k/2} * T_i(1.2 sqrt(beta)) * G_j
    (G_j a beta-free constant, k >= i+j, p >= 0.58), using
    T_i(R) <= R^{i-1} e^{-p R^2/2} (1/p)(1 + (i-1)/(p R^2) + ...),
    show f is decreasing for beta >= 15.  (Sufficient: the log-
    derivative (2 - k/2 + (i-1)/2)/beta - 0.72 p < 0 at beta = 15
    given the exponent bound from L3; state the worst exponent.)

Answer format: four lines "Ln: PASS/FAIL - <derivation sketch>",
then one line "OVERALL: ..." with anything you would flag.
