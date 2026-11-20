# The critical high-success window for stopped benchmark scores

Take the pooled experiment and score \(Z\) in [the variance bound](sharp-boundary-decay.md). The cap \(n\ge2\) is fixed while \(m\to\infty\). Put \(L=m^{1-1/n}\), with \(q_i\) the failure probability on task \(i\). Suppose \(\sum_i q_i=O(L)\). Define
\[
 B=\prod_i(1-q_i^n),\qquad
 \mu_m=L^{-1}\sum_i\frac{\sum_{j=0}^{n-1}j q_i^j}{\sum_{j=0}^{n-1}q_i^j}.
\]
Then the full-budget target \(P=\Pr(S\ge m)\) tends to one and
\[
 E Z = B\left(\exp(\mu_m^n)+o(1)\right).
\]
The error inside parentheses tends to zero even when \(B\) tends to zero. Probabilities may equal zero or one. A task that always misses gives \(B=EZ=0\).

In particular, take \(q_i=m^{-1/n}\theta_i\) with uniformly bounded nonnegative \(\theta_i\). If the empirical first and \(n\)-th moments of the \(\theta_i\) tend to \(u\) and \(v\), respectively, then
\[
 E Z/P\ \longrightarrow\ \exp(u^n-v).
\]
For \(n=2\) the exponent is minus the limiting variance of the rescaled failure probabilities. More generally the exponent is the negative Jensen gap for the \(n\)-th power. Even vanishing between-task variance can leave a nonvanishing calibration error.

**Example.** With two attempts per task, let half the tasks be certain to succeed and the others have failure probability \(2/\sqrt m\), for even \(m\ge4\). The certain tasks alone give \(m\) full successes, so \(P=1\) exactly. Yet \(EZ\to e^{-1}\). This concerns the expected stopped score for a pooled total under independent attempts.

**Composition limit.** Write \(w_s=\binom{m+s-1}{s}/[z^s](1+\dots+z^{n-1})^m\) for a feasible total of \(s\) observed failures. Its reciprocal is the probability that a uniform weak composition of \(s\) into \(m\) parts has every part below \(n\). If \(s/L\to x\in[0,\infty)\), the probability tends to \(\exp(-x^n)\). Indeed the \(j\)-th falling factorial moment of the number of parts at least \(n\) is
\[
 (m)_j\frac{(s)_{nj}}{(s+m-1)_{nj}},
\]
using falling factorials and zero when \(s<nj\). Subtract \(n\) units from each of \(j\) specified distinct parts to obtain the formula. For every fixed \(j\ge1\) it tends to \(x^{nj}\), including when \(x=0\) by bounding the numerator by \(s^{nj}\). The finite inclusion-exclusion upper and lower bounds for zero such parts then converge to the alternating exponential series as their truncation grows. For every finite \(K\),
\[
 \sup_{0\le s\le KL}|w_s-\exp((s/L)^n)|\to0.
\]
Otherwise a sequence violating the bound would have a subsequence with \(s/L\) convergent in \([0,K]\). The composition threshold is a known ingredient. Bevan and Threlfall study this threshold for parts of fixed size; the factorial-moment argument supplies the fixed-total formulation used here. [On the evolution of random integer compositions](https://doi.org/10.37236/13010).

**Random waits.** Define independent auxiliary waits \(U_i\in\{0,\ldots,n-1\}\) with masses proportional to \(q_i^j\), including the continuous extension at \(q_i=1\), and let \(W=\sum_iU_i\). Multiplying these probabilities by the all-hit probability gives the exact identity \(EZ=B\,E w_W\). Each \(E U_i^2\le q_i\sum_{j=1}^{n-1}j^2\), so \(\operatorname{Var}(W)=O(L)\). Consequently \(W/L-\mu_m\to0\) in probability, with \(\mu_m\) bounded.

Control of the large-score tail is needed to pass from this concentration to expectation. Uniformly in feasible \(s\), \(w_s\le D_n^s\) with \(D_n=2^{2n}\). For \(s\le m/2\) the cap admits every zero-one composition, and the ratio to their count is at most \(3^s\) by termwise comparison of the binomial products. For \(s>m/2\), the numerator is at most \(2^{mn}\) and the denominator at least one. For any fixed \(t>0\),
\[
 E e^{tW}\le\exp\!\left(\sum_i q_i \sum_{j=1}^{n-1}(e^{tj}-1)\right).
\]
This follows from \(q_i^j\le q_i\) for \(j\ge1\). Hence \(E[w_W;W>KL]\le e^{-KL}E[(eD_n)^W]\to0\) for sufficiently large fixed \(K\). Take \(K>\sup_m\mu_m+1\) as well. On \(W\le KL\) use the uniform composition limit and uniform continuity of the exponential function on the compact range of \((W/L)^n\). This gives \(Ew_W-\exp(\mu_m^n)\to0\). The expected number of full failures is \(n\sum q_i=O(L)=o(m)\); Markov's inequality gives \(P\to1\).

For the bounded rescaling, \(\sum q_i^2/L=o(1)\) and the auxiliary mean per task equals \(q_i+O_n(q_i^2)\). Thus \(\mu_m\to u\). Moreover \(\max q_i^n=O(1/m)\) and \(\sum q_i^n\to v\), yielding \(\log B\to-v\). Substitution proves the second formula.

**Relation to the benchmark literature.** The fixed-total composition limit is not claimed as new. The stopped-score identity, its integration against heterogeneous waits with control of the unbounded weights, and the resulting calibration formula are the content of this supplement. The benchmark target sums repeat successes across tasks. Chen et al. estimate the probability of at least one solution separately per problem from uncensored samples. The example makes no empirical claim about an AI model. This note extends the same manuscript, with no assessment transferred from an earlier PDF. [Evaluating Large Language Models Trained on Code, Appendix A](https://arxiv.org/abs/2107.03374).
