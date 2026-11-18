# A pointwise neighbourhood of spectral recovery without exact quotient symmetry

Retain half-noise and the notation of the [rank-defect estimate](RANK-DEFECT-AND-SPECTRAL-TRAPS.md). Suppose a positive reference probability density \(\pi_0\) has \(\|\pi_0\|_2\le B\) and depends on a binary quotient with four disjoint column families of rank deficit at most \(r\). For another positive probability density \(\pi\), assume exact ambient Walsh matching to order \(k\ge1\) and
\[
 \|\log(\pi/\pi_0)\|_\infty\le 1/4096 .
\]
There is no requirement of matching for \(\pi_0\), symmetry for \(\pi\), or a common positive floor. For the actual chain with stationary density \(\pi\),
\[
 \max_j |\lambda_j(K)-\lambda_j(P)|\le
 \min\{1,C_B 2^{33r-3k/224}\}.
\]
In particular a fixed-width relative neighbourhood of a four-basis quotient law has exponential recovery along matched densities, even when their Walsh spans are the full ambient space. The width and exponents are sufficient values.

## Stability of positive symmetric scaling

For \(f=\log(\pi/\pi_0)\), let \(\epsilon=\|f\|_\infty\) and \(\pi_t=\pi_0 e^{tf}\), without renormalizing along the path. Write \(h_t P h_t=\pi_t\) (pointwise product). Existence and smooth dependence in finite dimension follow by minimizing
\[
 \tfrac12\sum_{x,y}\mu(x)P(x,y)e^{u(x)+u(y)}
 -\sum_x\mu(x)\pi_t(x)u(x).
\]
Positive diagonal terms already give a coercive lower bound and a positive definite Hessian. The minimizer has \(h_t=e^u\); the implicit function theorem applies. The associated \(K_t\) is Markov, reversible, and positive semidefinite in \(L^2(\pi_t\,d\mu)\) by stationary conjugation and positivity of the Boolean noise spectrum. Differentiating gives
\[
 (I+K_t)\,\partial_t\log h_t=f .
\]
The operator \(H_t=(I-K_t)/2\) has \(L^2\) norm at most \(1/2\) and \(L^\infty\) norm at most one. Interpolation and the geometric series for \((I+K_t)^{-1}=(I-H_t)^{-1}/2\) give \(L^p\) operator norm at most \(1/[2(1-2^{-2/p})]\le p\) for \(2\le p<\infty\). Comparing the path measures to \(\pi_0\) and integrating yields, for \(v=\log(h_1/h_0)\),
\[
 \|v\|_{L^p(\pi_0)}\le e^{2\epsilon/p}p\epsilon\le2p\epsilon .
\]
Here and below \(L^p(\pi_0)\) uses probability measure \(\pi_0d\mu\). Expanding the exponential, the terms of order \(j\ge2\) in \(E_{\pi_0}e^{168|v|}\) are bounded by \((336e\epsilon)^j\) using \(j!\ge(j/e)^j\); the first moment is bounded by the second. Thus \(e^{2v-f}\) has uniformly bounded \(L^{84}(\pi_0)\) norm. This estimate concerns stationary scaling, and uses a finite-\(p\) bound with constants independent of small atom masses. For related stability theory see [Nutz and Wiesel](https://www.math.columbia.edu/~mnutz/docs/stabilityOfPotentials.pdf).

## A reserve of integrability for arbitrary ambient test vectors

Put \(g_0=Ph_0\), \(F_0=Qh_0\), \(a_0=Eh_0\). Normalization gives \(\|F_0\|_2=1\) and \(\|g_0\|_2\le1\). Cauchy-Schwarz in \(h_0d\mu\) yields \(1\le a_0 E\pi_0g_0\le a_0B\). The inverse-moment proof from the rank-defect estimate therefore gives
\(\|g_0^{-1}\|_7\le C_B2^{16r}\) even without matching of the reference.

For \(q=21/20\) and every ambient unit \(L^2\) vector \(x\), we claim
\[
 \|g_0^{-2}|Qx|^2\|_{L^q(\pi_0)}\le C_B 2^{33r}.
\]
In \(Q=P_\lambda P_\gamma\) take \(\gamma^2=10/11\), \(\lambda^2=11/20\). Ordinary ambient hypercontractivity gives \(\|P_\gamma x\|_{2q}\le1\). Jensen gives \(|Qx|^q\le P_\lambda |P_\gamma x|^q\), whose input has \(L^2\) norm at most one. The weight \(W=\pi_0g_0^{-2q}\) is a quotient function, with
\[
 \|W\|_{5/4}\le B\|g_0^{-1}\|_7^{2q},
 \qquad 4/5=1/2+2q/7 .
\]
For this weight, the full-space multiplier bound at \(P_\lambda\) applies since \(10\le1+(20/11)^4\). It costs \(2^{4r/5}\). Taking the \(q\)th root gives the claim because \(32+4/(5q)<33\). The same proof with \(W=\pi_0\) bounds \(\||Qx|^2\|_{L^q(\pi_0)}\) by \(C_B2^{33r}\).

## The perturbed chain

The identity \(U=\pi_0g_0^{-2}e^{2v-f}\) transports the preceding reserve to any set \(E\), including sets that cut every quotient fibre. Hölder with exponents \(84,21/20,28\) gives
\[
 E[\mathbf1_E U |Qx|^2]\le C_B 2^{33r}\pi_0(E)^{1/28}
 \le C_B2^{33r}\mu(E)^{1/56}.
\]
The notation \(\pi_0(E)\) means \(\int_E\pi_0d\mu\). The same bound holds with \(\pi\) instead of \(U\), by \(\pi\le e^\epsilon\pi_0\). The three reciprocal exponents are \(1/84,80/84,3/84\).

Apply the matching-energy estimate to the true \(\pi\), whose second moment norm is at most \(e^\epsilon B\). For \(E=\{|Ph_1-1|>2^{-k/8}\}\), it gives \(\mu(E)\le C_B 2^{-3k/4}\). On its complement \(|U-\pi|\le C 2^{-k/8}\pi\) for large \(k\). Combining the two estimates yields \(\|QM_{U-\pi}Q\|\le C_B 2^{33r-3k/224}\). For the signed term \(QM_{\pi-1}Q\), the two low factors vanish by true matching. The positive quotient envelope \(1+e^\epsilon\pi_0\) dominates \(|\pi-1|\), so the same split at ambient degree \(\lfloor k/2\rfloor\) as in the rank-defect note bounds the remainder by \(C_B2^{r/2-(\lfloor k/2\rfloor+1)/4}\). The Gram argument proves the asserted spectral bound for all ordered eigenvalues. Bounded \(k\) is absorbed into the constant.

## A full-span check and the boundary of the conclusion

Let \(L=3m,\ m\ge4\), let \(S\) be the first \(m\) coordinates, and let \(w\) be the remaining \(2m\) coordinates. Take
\[
 \pi_0=1+(1-a_m)\chi_S,\qquad
 H=(\chi_w+\textstyle\sum_{i=1}^L\chi_{w\triangle\{i\}})/(L+1),
 \qquad \pi=\pi_0(1+H/16384),
\]
where \(0<a_m<1\) tends to zero. The reference has four disjoint column bases of rank one and norm at most two. Since \(|H|\le1\), the log ratio bound holds. Every new character and its product with \(\chi_S\) has degree at least \(2m-1\). Hence \(\pi\) is normalized and matches through \(m-1\). All displayed nonconstant coefficients are positive and the pairs \(w,w\triangle\{i\}\) generate every singleton in the Walsh span. Its intrinsic deficit is \(\lceil3L/4\rceil\), making the exact-code estimate uninformative here. Yet the new result bounds the full spectral error by \(C 2^{-3(m-1)/224}\), although \(\min\pi\le(1+1/16384)a_m\to0\).

The [metastable shell](https://airr.science/papers/ARR-2026-2B2W1WQ7DF9N5VW7/versions/v1/) is arbitrarily close to the uniform law in cubic mean and has a macroscopic discrepancy in its second eigenvalue. Thus small cubic-mean error cannot replace this pointwise log-ratio condition, even around the uniform law. What remains undecided is recovery for arbitrary matched laws at the programme's stationary moment endpoint, outside the neighbourhood controlled here. These notes belong together as one research development. The proof is analytic and ungraded; the frozen AIRR revision and its assessment predate it.
