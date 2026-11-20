# Two attempts: exact integral and decay beyond the critical window

Let \(n=2\) in [the stopped experiment](critical-window.md), let \(b=m^{-1}\sum p_i\), \(V=m^{-1}\sum(p_i-b)^2\), and write \(P_b=\Pr(\mathrm{Bin}(2m,b)\ge m)\). Then
\[
 E Z=m\binom{2m}{m}\left(\prod_i p_i\right)
      \int_0^1 u^{m-1}\prod_i(1-u p_i)\,du.
\]
In particular, whenever \(b>0\),
\[
 E Z\le P_b\frac{\prod_i p_i}{b^m}
 \le P_b\exp[-mV/(2p_{\max}^2)].
\]
This bound has no polynomial prefactor. Its reference \(P_b\) is the homogeneous binomial tail. When some task is impossible the left side vanishes. When all tasks are impossible the score and target vanish.

**Proof.** For \(s\) late hits on an all-hit log the weight is \(w_s=\binom{m+s-1}{s}/\binom ms\). Euler's beta integral gives
\[
 w_s=m\binom{2m}{m}\int_0^1 u^{m+s-1}(1-u)^{m-s}\,du.
\]
Each early hit has probability \(p_i\); each late hit has probability \(p_i(1-p_i)\). Summing the integral over the choices of late-hit labels gives the displayed identity. For each \(u\), arithmetic-geometric mean gives \(\prod_i(1-up_i)\le(1-ub)^m\). Equal probabilities give \(E Z=P_b\) by homogeneous unbiasedness, also directly by the incomplete beta integral. The curvature of \(\log p\) on \((0,p_{\max}]\) is at most \(-1/p_{\max}^2\). Taylor's inequality at \(b\) and cancellation of the linear terms give the second bound. [Euler's beta integral, NIST](https://dlmf.nist.gov/5.12).

**Exact asymptotic rate.** Suppose in a triangular array that \(b\to b_*>1/2\) (including \(b_*=1\)), \(\max_i|p_i-b|\to0\), and \(\liminf mV>0\). With \(P\) the actual heterogeneous full tail,
\[
 \frac{\log(EZ/P)}{mV}\ \longrightarrow\ -\frac{1}{b_*^2}.
\]
Thus at high success rates a divergence of \(mV\), however slow, is sufficient for collapse at cap two. If \(mV\to\tau\in(0,\infty)\), the limiting ratio is \(\exp(-\tau/b_*^2)\). If \(mV\to0\) under the same conditions on the mean and the largest deviation, the ratio tends to one.

To prove this, substitute \(x=bu\) and divide the integral by its homogeneous counterpart. This gives the conditional expectation, for \(X\sim{\rm Beta}(m,m+1)\) given \(X\le b\), of
\[
 H(X)=\prod_i(1+\delta_i/b)
         \left(1-\frac{X\delta_i}{b(1-X)}\right),\qquad \delta_i=p_i-b.
\]
Both product factors are separately bounded by one by arithmetic-geometric mean and are nonnegative on the integration interval. For any fixed small \(\epsilon>0\), the conditional probability that \(|X-1/2|>\epsilon\) decays exponentially in \(m\). Indeed the density is proportional to \([x(1-x)]^{m-1}(1-x)\); compare the maximum outside the band to the minimum on a smaller band around \(1/2\) contained in \([0,b]\). On the central band,
\[
 \log H(x)=-\frac{mV}{2b^2}\left(1+\frac{x^2}{(1-x)^2}\right)
             +O_\epsilon(mV\max_i|\delta_i|).
\]
Both linear terms sum to zero. The sum of the absolute cubic remainders is bounded using \(\sum|\delta_i|^3\le mV\max|\delta_i|\). Bounding the integral above and below on this band and using \(0\le H\le1\) off it yields the limit: \(mV=o(m)\), so the exponentially small tail is negligible even compared with \(\exp(-C mV)\). Shrink \(\epsilon\) to zero after taking the row limit. For \(mV\to0\) the central integrand tends uniformly to one. Finally both \(P_b\) and \(P\) tend to one by the variance bound for independent Bernoulli trials since \(b_*>1/2\). For \(\liminf mV>0\) their log corrections divided by \(mV\) vanish.

**Obstruction at higher caps.** The beta argument represents \(w_s\) as moments of one nonnegative random variable \(X/(1-X)\) before conditioning, with \(X\sim\mathrm{Beta}(m,m+1)\). At every cap \(n\ge3\), \(m\ge2\), the finite sequence has \(w_0=w_1=w_2=1\) but \(w_n>1\): at total \(n\) the cap excludes the \(m\) compositions with an entry \(n\) and leaves other compositions. Any probability law with first two moments one has variance zero and every moment one. Hence this one-variable positive moment representation cannot extend to higher caps. Other integral or direct coefficient arguments remain possible.
