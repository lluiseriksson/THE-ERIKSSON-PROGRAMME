# The sharp variance power at the high-success boundary

Use the independent, equally capped experiment of [the preceding note](persistent-heterogeneity.md). There are \(m\) tasks and \(n\ge2\) potential Bernoulli trials per task. The probability on task \(i\) is \(p_i\in[0,1]\). Write \(S\) for the full success count, \(P=\Pr(S\ge m)\), \(q_i=1-p_i\), \(a=m^{-1}\sum_iq_i\) and \(V=m^{-1}\sum_i(q_i-a)^2\). The homogeneous first-success score \(Z\) is zero if any task misses. Otherwise it is the ratio of the numbers of unrestricted and capped compositions of the total wait into \(m\) parts. In particular it is at least one whenever all tasks hit.

**Theorem.** For each common cap \(n\) there is \(C_n>0\) such that on the entire closed probability cube
\[
 E Z\ \le\ P(mn+1)^5
 \exp\{-C_n m V\max(a,\sqrt V)^{n-2}\}.
\]
For \(n=2\) the factor raised to zero is one. Thus any fixed positive variance gives exponential decay on the relative scale wherever \(P>0\), including arbitrarily rare full tails. If \(E S\le m\), the exponent can be taken to be \(-c_n mV\) even for rows approaching the boundary. Without restrictions on the mean, the power \(n/2\) in the weaker variance-only exponent \(-C_n m V^{n/2}\) is optimal among exponents accompanied by a fixed polynomial prefactor in \(m\).

**Loss of the coefficient profile.** Use the coefficient bound in steps 1–3 of the preceding note. For its degree-\(n\) polynomial \(F_c(q)=(1-q)\sum_{j=0}^{n-1}(cq)^j\), let \(v\) be its interior maximizer, \(c>1\) and \(R_v(q)=F_c(q)/F_c(v)\). Write
\[
 F_c'(u)=\sum_{j=0}^{n-2} b_j u^j - n c^{n-1}u^{n-1},\qquad b_j>0.
\]
At \(u=v\) the two terms balance. For \(u\ge v\), each positive monomial is at most its value at \(v\) times \((u/v)^{n-2}\). For \(u\le v\) the inequality reverses. Hence \(F_c'\) points towards \(v\), with magnitude at least \(n c^{n-1}u^{n-2}|u-v|\). Since \(F_c(v)\le n c^{n-1}\), integration gives
\[
 1-R_v(q)\ \ge\ B_n(q+v)^{n-2}(q-v)^2,\qquad B_n=2^{-(n-2)}/8 .
\]
Indeed integrate on the half of the interval between \(v\) and \(q\) nearer the larger endpoint. There \(u\ge(q+v)/2\), and the integral of \(|u-v|\) on that half is at least \((q-v)^2/8\). Continuity of the normalized endpoint profiles gives the same inequality at \(v=0,(n-1)/n\).

**Averaging.** Let \(H=m^{-1}\sum_i(q_i+v)^{n-2}(q_i-v)^2\). Since \(q_i+v\ge|q_i-v|\), the power-mean inequality gives \(H\ge[V+(a-v)^2]^{n/2}\). In particular \(H\ge V^{n/2}\). If \(v\ge a/2\), the definition gives \(H\ge(a/2)^{n-2}V\). If \(v<a/2\), the same inequality follows from the power-mean bound because \(V+(a-v)^2\) is at least both \(V\) and \(a^2/4\). Using \(R_v\le\exp[-(1-R_v)]\), summing the coefficient bound over all waits yields
\[
 E Z\le (mn+1)^3\exp[-A_n m V\max(a,\sqrt V)^{n-2}],
 \qquad A_n=B_n2^{-(n-2)}.
\]
For \(E S\ge m\) the integer support gives \(P\ge1/(mn+1)\), which proves the relative bound in this regime.

**Rare tails.** First take all probabilities interior and \(E S<m\). Multiply all odds by \(\lambda>1\) so the new success probabilities \(y_i\) have mean \(t=1/n\). The inverse map \(g(y)=y/[\lambda-(\lambda-1)y]\) obeys
\[
 |g(y)-g(t)|
 =\frac{\lambda|y-t|}{[\lambda-(\lambda-1)y][\lambda-(\lambda-1)t]}
 \le \frac{|y-t|}{1-t}.
\]
Centering at \(g(t)\) bounds \(V\le V_\lambda/(1-t)^2\). The new mean failure probability is \(1-t\). The full-data likelihood ratio is \(K\lambda^{-S}\), and \(Z\) is supported on \(S\ge m\). It follows that \(EZ/P\le E_\lambda Z/\Pr_\lambda(S=m)\). The integer-mean atom bound for the log-concave sum yields \(\Pr_\lambda(S=m)\ge(mn+1)^{-2}\). Apply the preceding absolute bound with \(a_\lambda=1-t\) to get the exponent \(-A_n(1-t)^n mV\). This also proves the displayed global inequality with \(C_n=A_n(1-t)^n\), since \(a,\sqrt V\le1\). For equality of the full mean with the threshold use \(\lambda=1\). Continuity extends the product inequality to all boundary rows; if \(P=0\), the support of \(Z\) gives \(EZ=0\) directly.

**Sharpness.** For even \(m\) put \(q_i=\varepsilon_m\) on half the tasks and \(q_i=2\varepsilon_m\) on the rest, with \(\varepsilon_m=m^{-\alpha}\) and sufficiently large \(m\). Then \(V=\varepsilon_m^2/4\). The union bound and the minimum score on all-hit records give
\[
 EZ/P\ge EZ\ge 1-m(2\varepsilon_m)^n.
\]
For any \(0<\beta<n/2\), choose \(1/n<\alpha<1/(2\beta)\). The right hand side tends to one, whereas \(mV^\beta\) grows as a positive power of \(m\). Thus any proposed uniform relative upper bound with exponent \(-c m V^\beta\), \(c>0\), and any fixed polynomial prefactor tends to zero on the same rows. This establishes the claimed sharpness even with every finite-row probability strictly between zero and one.

**Use and scope.** The theorem gives a sufficient condition for the stopped score to lose calibration against the pooled full-budget target. The example rules out inferring this collapse from \(mV\gg\log m\) alone for \(n>2\) when tasks become nearly certain. Independence within and across tasks is essential to this experiment. A benchmark measuring the chance of at least one success separately for each task uses a different target. The finite sign problem in the middle strata remains open.

The coefficient reduction and atom bound are documented in the preceding note. The classical convolution result is due to the log-concavity literature. The benchmark comparison uses the estimator defined by Chen and colleagues. The accompanying exact rational checks exercise the polynomial inequality and inverse tilt separately from the analytic proof. This supplement has no separate editorial assessment. [Johnson and Goldschmidt](https://doi.org/10.1051/ps:2006008). [Chen et al., Appendix A](https://arxiv.org/abs/2107.03374).
