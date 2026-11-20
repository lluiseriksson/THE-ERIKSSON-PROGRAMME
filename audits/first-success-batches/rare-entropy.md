# A multiplicative equivalent for heterogeneous rare pooled tails

There are \(m\) independent tasks with fixed attempt cap \(n\ge2\). Within each task the trials are independent with success probability \(p_i\). Let \(P=\Pr(S\ge m)\) be the full pooled target and \(Z\) the homogeneous first-success score. This note compares two small quantities on the relative scale. Assume \(0<p_i\le b<a=1/n\) for a constant \(b\) independent of the row. Write \(q_i=1-p_i\), let a bar denote the empirical mean across tasks, and choose the unique \(\lambda>1\) such that
\[
 y_i=\frac{\lambda p_i}{q_i+\lambda p_i},\qquad \bar y=a.
\]
Assume \(v_m=n\sum_i y_i(1-y_i)\to\infty\). This holds, for example, if the original probabilities stay in a compact subinterval of \((0,a)\). No uniform positive lower bound is needed when the tilted variance condition can be verified directly.

**Equivalent.** Write \(D(a\|y)=a\log(a/y)+(1-a)\log((1-a)/(1-y))\). Then
\[
 \frac{EZ}{P}=(1+o(1))\,K_m\,\exp\!\left\{-n\sum_i D(a\|y_i)\right\},\qquad
 K_m=\frac{a(1-\lambda^{-1})}{1-(1-a)\overline{q_i^{-1}}}
 \sqrt{\frac{\overline{y_i(1-y_i)}}{a(1-a)}} .
\]
The denominator of \(K_m\) is uniformly positive. The equivalent allows varying probability profiles, without a limiting empirical distribution. It is an asymptotic identity for the stated rare regime.

**Near a homogeneous row.** Suppose \(\bar p\to p\in(0,1/n)\), \(\max_i|p_i-\bar p|\to0\) and \(V=m^{-1}\sum_i(p_i-\bar p)^2\). Then
\[
 \log(EZ/P)=-\left(\frac{n-1}{2n p^2(1-p)^2}+o(1)\right)mV+o(1).
\]
In particular the ratio tends to one, to \(\exp[-(n-1)\tau/(2n p^2(1-p)^2)]\), or to zero according as \(mV\) tends to zero, \(\tau\in(0,\infty)\), or infinity. The last conclusion holds for arbitrarily slow divergence. The cap-three family with half the tasks at \(1/4-1/(8\sqrt m)\) and half at \(1/4+1/(8\sqrt m)\) has limiting ratio \(e^{-4/27}\), even though all task differences tend to zero and the full target itself is rare.

**1. The stopped mean near the last possible wait.** Set \(L=m(n-1)\), \(C_s=\binom{m+s-1}{s}\), and let \(A_m(d)\) count capped compositions of \(d\) with all coordinates at most \(n-1\). Dividing the mean by \(C_L\prod_i p_i q_i^{n-1}\) gives exactly
\[
 \sum_{d=0}^L\frac{(L)_d}{(L+m-1)_d}\,
   \frac{1}{A_m(d)}\sum_{\substack{\sum e_i=d\\0\le e_i<n}}
     \prod_i q_i^{-e_i}.
\]
Here \(d\) counts the distance from the last possible total wait, and \((z)_d\) denotes a falling factorial. For fixed \(d\) the fraction of capped compositions with a repeated index is \(O_d(1/m)\): the all-distinct choices already contribute \(\binom md\), while the unrestricted count is \(\binom{m+d-1}d\). The product is uniformly bounded for fixed \(d\). On the all-distinct choices the average differs from \((\overline{q_i^{-1}})^d\) by \(O_{b,d}(1/m)\), since \(d\) draws with replacement have a collision with probability \(O_d(1/m)\). The falling factorial ratio tends to \((1-a)^d\). For all large \(m\) the terms of the sum are bounded by a geometric sequence with fixed ratio strictly less than one, since \(q_i^{-1}\le1/(1-b)\) and \(L/(L+m-1)\to1-a\). The approximating series has the same type of bound. Splitting both series at a fixed large \(d\) therefore gives their difference tending to zero:
\[
 EZ=(1+o(1))\, C_L\frac{\prod_i p_i q_i^{n-1}}{1-(1-a)\overline{q_i^{-1}}}.
\]

**2. The full tail.** Under the exponential tilt by \(\lambda^S\), the full count has integer mean \(m\) and variance \(v_m\). Likelihood inversion gives
\[
 P=\lambda^{-m}\prod_i(q_i+\lambda p_i)^n
    \sum_{j\ge0}\lambda^{-j}\Pr_\lambda(S=m+j).
\]
For each bounded \(j\), \(\sqrt{2\pi v_m}\Pr_\lambda(S=m+j)\to1\). Also all point masses are \(O(v_m^{-1/2})\). For completeness, a Bernoulli characteristic function has squared modulus \(1-4y(1-y)\sin^2(t/2)\), so the product modulus is bounded by \(\exp[-2v_m\sin^2(t/2)]\). On scaling \(t=z/\sqrt{v_m}\), the centered product tends to \(e^{-z^2/2}\): on a fixed neighborhood of zero each log characteristic function has centered quadratic term \(-y(1-y)t^2/2\) and remainder \(O(y(1-y)|t|^3)\) uniformly in \(y\). The sine bound gives an integrable Gaussian envelope on the scaled inversion interval. Fourier inversion and dominated convergence prove both assertions. As \(\lambda\ge a(1-b)/[(1-a)b]>1\), geometric domination yields a tail factor \((1+o(1))/[(1-\lambda^{-1})\sqrt{2\pi v_m}]\). This local-limit change of measure is a classical lattice large-deviation technique. [Chaganty and Sethuraman, 1993](https://doi.org/10.1214/aop/1176989136).

**3. Assemble and expand.** Stirling's formula applied to \(C_L=a\binom{mn}{m}\) and \(y_i/(1-y_i)=\lambda p_i/q_i\) reduces the ratio of exponential factors to
\[
 \prod_i(y_i/a)\,[(1-y_i)/(1-a)]^{n-1}.
\]
The remaining factors give \(K_m\). In the near-homogeneous limit \(\lambda\to a(1-p)/[(1-a)p]\) by bracketing the mean with the smallest and largest probabilities. Hence \(K_m\to1\). The derivative of the tilt in \(p_i\) tends uniformly on that shrinking interval to \(a(1-a)/[p(1-p)]\). The pairwise variance identity then gives \(\sum_i(y_i-a)^2=(mV)([a(1-a)/(p(1-p))]^2+o(1))\). Taylor expansion of \(D(a\|y)\) gives the stated constant. With zero variance the ratio is exactly one by homogeneous calibration.

**Interpretation.** The relative law quantifies changes in a pooled first-success score in an independent-trial experiment below threshold. It gives no empirical estimate for an AI system. The primary classical comparison is the tilted lattice tail theorem above; the boundary-wait normalization and its combination with the full-tail equivalent are specific to this score. The [exceptional-task note](exceptional-tasks.md) separately covers a fixed number of tasks crossing the subthreshold ceiling, including tasks with certain success. The present result is subsequent to the assessed manuscript and has no separate AIRR rating.
