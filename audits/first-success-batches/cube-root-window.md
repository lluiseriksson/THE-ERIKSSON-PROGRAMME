# When the fixed-task approximation first fails

In the [first-success experiment](sparse-threshold.md), give each of \(m\) tasks two independent Bernoulli attempts. The background success probability is \(1/2\). Replace \(r\ge1\) tasks by certain successes. Let \(P\) be the probability of at least \(m\) total successes in all \(2m\) trials and \(EZ\) the mean of the homogeneous score evaluated on the stopped logs. Define
\[
 G_{m,r}=\frac{4^r\Gamma((r+1)/2)}{\sqrt{\pi}\,m^{r/2}},\qquad L=r\sqrt{r/m}.
\]
For fixed \(r\), \(G_{m,r}\) is the leading approximation to \(EZ/P\). The following gives a threshold for its relative accuracy as \(r\) grows, distinct from the leading logarithmic rate.

* If \(r/m^{1/3}\to c\in[0,\infty)\), then \((EZ/P)/G_{m,r}\to\exp(-c^{3/2}/\sqrt2)\).
* If \(m^{1/3}\ll r\ll m\), then \(\log[(EZ/P)/G_{m,r}]/L\to-1/\sqrt2\).

In particular, substituting a growing \(r\) directly into the fixed-task formula overestimates the score-to-target ratio by an unbounded factor above the cube-root scale. At \(r\sim m^{1/3}\) the limiting ratio to that approximation is already \(e^{-1/\sqrt2}\). The result concerns an independent-trial model and its specified score.

**Exact reduction.** Substitute these probabilities and \(v=1-u\) into the [two-attempt integral](two-attempt-integral.md). With \(C_m=m\binom{2m}{m}/4^m\) this gives exactly
\[
 EZ=C_m4^r\int_0^1 v^r(1-v^2)^{m-1}(1+v)^{1-r}\,dv .
\]
Let \(\alpha=(r+1)/2\) and \(U\sim{\rm Beta}(\alpha,m)\). The substitution \(u=v^2\) turns the integral into \(\frac12 B(\alpha,m)E(1+\sqrt U)^{1-r}\). Consequently
\[
 \frac{EZ/P}{G_{m,r}}=
 \frac{C_m\sqrt{\pi/m}}{2P}\,
 \frac{m^\alpha\Gamma(m)}{\Gamma(m+\alpha)}\,
 E(1+\sqrt U)^{1-r}.
\]
In particular for \(r=1\) the expectation and the gamma factor are identically one, giving \(EZ=2\binom{2m}{m}/4^m\), also obtained by integrating \(v(1-v^2)^{m-1}\) directly. [Euler's beta integral](https://dlmf.nist.gov/5.12).

**Prefactors.** Stirling's formula gives \(C_m\sqrt{\pi/m}\to1\) and
\[
 \log[m^\alpha\Gamma(m)/\Gamma(m+\alpha)]=O((\alpha+\alpha^2)/m+1/m)
\]
uniformly for \(\alpha=o(m)\), by expanding \(\log(1+\alpha/m)\). Since the replacements improve the full experiment, \(1/2\le P\le1\) for every row by binomial symmetry and coupling. The exact distribution of successes is \(2r+\operatorname{Bin}(2(m-r),1/2)\); the central limit theorem gives \(P\to1/2\) for \(r=o(\sqrt m)\). Thus the two prefactors together tend to one on and below the cube-root scale. Above that scale their logarithm is \(o(L)\).

**The remaining expectation.** For diverging \(r=o(m)\), write \(U=X/(X+Y)\) with independent unit-scale gamma variables of shapes \(\alpha\) and \(m\). This representation follows by changing variables in the joint density. For any fixed relative tolerance, Markov's inequality applied to the gamma moment-generating function bounds the probability of a relative deviation of either gamma by \(C_\epsilon e^{-c_\epsilon r}\). Hence, off an event of that probability, \(\sqrt U/\sqrt{r/(2m)}\) is between \(1-\epsilon\) and \(1+\epsilon\) for sufficiently large \(m\) (take tighter tolerances for the gammas). In particular \((r-1)\log(1+\sqrt U)/L\to 1/\sqrt2\) in probability.

For \(L\) bounded and converging, the integrand is bounded by one and converges in probability to \(\exp[-\lim L/\sqrt2]\). For bounded \(r\) the integrand instead tends directly to one because \(EU=\alpha/(m+\alpha)\to0\). For \(L\to\infty\) use the same exponential deviation estimate. On the good event the log integrand is within \(O(\epsilon L)+o(L)\) of \(-L/\sqrt2\). The bad event contributes at most \(C_\epsilon e^{-c_\epsilon r}\), negligible because \(L=o(r)\). Taking logs and then shrinking \(\epsilon\) proves the second limit.

The cube-root scale comes from multiplying the typical beta-coordinate size \(\sqrt{r/(2m)}\) by the \(r-1\) factors in the exact integrand. This argument supplements the reviewed manuscript. Its assessment has not been carried over to this result.
