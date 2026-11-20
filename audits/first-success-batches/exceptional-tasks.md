# Fixed exceptional tasks at and below the pooled threshold

Consider the first-success score in the [manuscript](paper-dilute.tex), with a fixed cap \(n\ge2\) and \(m\) tasks. The full target is \(P=\Pr(S\ge m)\). In the reference bank each trial succeeds with probability \(p_m\), independently. Replace a fixed number \(r\ge1\) of tasks by tasks with failure probabilities \(x_i\). Attempts remain independent; only the parameters change. Let \(Z\) denote the canonical score applied to these logs. It is zero unless every task hits and otherwise weights the sum of waits \(s\) by the unrestricted-to-capped composition ratio \(w_s\).

**A single certain task.** For a fixed background \(p<1/n\) and one replacement with success probability one, the score-to-target ratio vanishes at order \(m^{-(n-1)}\). For \(p=1/n\) it vanishes at order \(m^{-(n-1)/2}\). For example at cap three the equivalents are \(24/m^2\) when \(p=1/6\), and \(18/m\) when \(p=1/3\). The full target strictly improves over that of the original homogeneous bank for all sufficiently large finite \(m\), by monotone coupling and a positive-probability pivotal event. Nevertheless the stopped mean divided by the **improved** target tends to zero. The between-task variance is of order \(1/m\). Thus this effect is not explained by a persistent positive variance.

**General replacement formula.** Write \(q_m=1-p_m\), \(h=r(n-1)\), \(a=1/n\), and put
\[
 H_m=\prod_{i=1}^r
 \left[a(1-x_i)/p_m+(1-a)x_i/q_m\right]^n.
\]
The following two regimes use different scales \(b_m\) and constants \(M_j\), with \(M_0=1\).

| Background | \(b_m\) | \(M_j\) |
|---|---|---|
| \(p_m=p<1/n\), \(0<p\) | \(m\) | \(j![\rho/(1-\rho)]^j\), \(\rho=(n-1)/(n(1-p))\) |
| \(\sqrt m(p_m-1/n)\to\kappa\in\mathbb R\) | \(\sqrt m\) | \(E[G^j\mid G\ge0]\), \(G\sim N(n^2\kappa,n(n-1))\) |

For \(\mathbf u=(u_1,\ldots,u_r)\in\{0,\ldots,n-1\}^r\) write \(|\mathbf u|=\sum u_i\). Uniformly over the replacement probabilities,
\[
 \frac{EZ}{P}=
 (1+o(1))\,
 \frac{\prod_i [(1-x_i)/p_m]}{H_m}
 \sum_{\mathbf u}
    \frac{M_{h-|\mathbf u|}}{b_m^{h-|\mathbf u|}}
    \prod_i(x_i/q_m)^{u_i}.
\]
The relative error applies when all \(x_i<1\); either side is zero if a replacement always fails. Consequently the formula also handles almost-certain replacements, including \(x_i\) on the scale \(1/b_m\). For fixed interior \(x_i\), only the top-wait term persists. Its limiting ratio is at most one, strictly below one when some \(x_i\) differs from the limiting background failure probability, by the arithmetic-geometric mean inequality with weights \(1/n,(n-1)/n\).

**1. Two reference laws.** Call the homogeneous full target \(P_0\). Under the homogeneous law weighted by \(Z/P_0\), the total wait \(s\) has probabilities proportional to \(\binom{m+s-1}{s}p_m^m q_m^s\) for \(0\le s\le L=m(n-1)\), by cancellation of the capped count. Conditional on \(s\), the wait vector is uniform over capped compositions. Thus \(D=L-s\) is the deficit of a negative-binomial wait conditioned to be at most \(L\). Conditional on \(D=d\), the vector of *individual deficits* \(n-1-u_i\) is a uniform capped composition of \(d\). The likelihood ratio of any all-hit log after the replacements is \(\prod_i[(1-x_i)/p_m](x_i/q_m)^{u_i}\).

For the full experiment use the reference law conditioned on \(S\ge m\). In both regimes \(S/(mn)\to a\) in probability under that law. Below the threshold the ratio of successive binomial masses from \(m\) onward is eventually bounded above by a constant below one. In the threshold window the central limit theorem keeps \(\Pr(S\ge m)\) bounded away from zero, while the unconditional fraction converges to \(a\). Given \(S\), the outcomes in the \(nr\) designated positions are sampled without replacement from \(S\) successes among \(mn\) positions. Every fixed pattern therefore has probability tending to its independent Bernoulli-\(a\) probability. The full likelihood ratio on these positions is a product of success factors \((1-x_i)/p_m\) and failure factors \(x_i/q_m\). Summing over finitely many patterns gives \(P/P_0=(1+o(1))H_m\), uniformly: the reference limiting pattern probabilities are all positive, and all likelihood terms are nonnegative.

**2. The deficit in the rare tail.** The mass at \(d\) relative to the mass at zero is
\[
 q_m^{-d}\frac{(L)_d}{(L+m-1)_d},\qquad (z)_j=z(z-1)\cdots(z-j+1).
\]
Its successive ratios are eventually bounded by some \(\rho'<1\) and for each fixed \(d\) it tends to \(\rho^d\). Hence \(D\) converges with every fixed factorial moment to the geometric distribution on \(0,1,\ldots\) with mass \((1-\rho)\rho^d\). Those moments are \(M_j\) in the table.

**3. The deficit in the threshold window.** Before conditioning, the total negative-binomial wait is a sum of \(m\) geometric variables with mean \(q_m/p_m\) and variance \(q_m/p_m^2\). The centered and scaled deficit \(D/\sqrt m\), with the centering already supplied by \(L\), has unconditioned Gaussian limit with mean \(n^2\kappa\) and variance \(n(n-1)\). Indeed the per-task third absolute moments are uniformly bounded, and \((L-mq_m/p_m)/\sqrt m\to n^2\kappa\). Conditioning on \(D\ge0\) gives the truncated law in the table. Moments of fixed orders also converge. The centered geometric moment-generating functions are bounded by \(\exp(Ct^2)\) uniformly in a neighborhood of zero because \(p_m\) stays in a compact interior interval. Applying this bound at \(t\) of order \(1/\sqrt m\) gives uniform integrability of every fixed power of the scaled deficit. Taking \(t\) of order \(\sqrt{\log m/m}\) gives a conditional probability \(O(m^{-A})\) of \(D>K\sqrt{m\log m}\) for any fixed \(A\) by choosing \(K\) large enough.

**4. Named coordinates.** Let \(A_k(d)=[z^d](1+\cdots+z^{n-1})^k\), understood as zero for negative \(d\). Fix \(r\) named deficits \(e_i=n-1-u_i\) of total \(j\). Their conditional probability is \(A_{m-r}(d-j)/A_m(d)\). In the rare case truncate at \(K\log m\); in the threshold window truncate at \(K\sqrt{m\log m}\). The discarded probability is \(o(b_m^{-j})\) with \(K\) chosen as above.

For \(n\ge3\) uniformly up to either cutoff, a uniform **unrestricted** composition of \(d\) violates the cap with probability at most \(m(d)_n/(m+d-1)_n=o(1)\). The same estimate applies after removing the named coordinates. For \(d\ge j\), the ratio of the unrestricted counts is
\[
 \frac{(d)_j(m-1)_r}{(m+d-1)_{r+j}}
 =(1+o(1))\frac{(d)_j}{m^j}.
\]
For \(n=2\) the exact capped probability is \((d)_j(m-d)_{r-j}/(m)_r\), with the same equivalent at either cutoff. For \(d<j\) both probabilities vanish. Integrating shows that the probability of the named wait pattern under the score-weighted law equals \((1+o(1))M_j/b_m^j\). Geometric tail domination or uniform integrability respectively also permits truncation of the factorial moments. Combining with the two likelihood ratios proves the formula. Each term has a relative estimate before summation, which is why probabilities \(x_i\) depending on \(m\) are allowed.

For certain replacements the only surviving wait pattern is \(\mathbf u=0\). At a fixed rare background the constant multiplying \(m^{-h}\) is \(p^{-r}(np)^{nr}M_h\). At the exact threshold the constant multiplying \(m^{-h/2}\) is \(n^r M_h\). For the two cap-three examples this gives 24 and 18.

**Scope.** The result measures a score in an independent Bernoulli experiment. The pooled target credits repeat successes on the same task. The composition argument uses the classical uniform allocation model studied by Bevan and Threlfall. The relative likelihoods and their constants apply to this particular stopped score. A literature comparison does not establish bibliographic priority. The finite-sample sign for all banks remains open. The accompanying arithmetic checks and note postdate the frozen v3 PDF; its assessment covers that PDF alone. [Bevan and Threlfall](https://doi.org/10.37236/13010). [Chen et al., per-task pass@k](https://arxiv.org/abs/2107.03374).
