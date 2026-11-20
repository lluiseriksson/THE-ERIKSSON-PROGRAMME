# One exceptional task at three attempts: a finite convex-order identity

Consider \(m\ge2\) tasks, each with three independent potential attempts. Different tasks are independent. Write \(S\) for the number of successes in the full experiment. Logs stop each task at the first success. The score \(Z\) is zero if any task misses on all attempts. Otherwise the weight at total wait \(s\) is the unrestricted number of weak compositions of \(s\) into \(m\) parts divided by the number with every part less than three. In the full experiment the target is the probability of \(S\ge m\).

**Finite comparison.** Let all but one task have success probability \(0<p<1\), and let the named task have success probability \(a\in[0,1]\). Define the stratum deficit
\[
 F_k(a)=\Pr_a(S=k)-E_a[Z\,1_{\{S=k\}}],\qquad m\le k\le3m.
\]
For every finite \(m\) and every such \(k\),
\[
 F_k(a)=(a-p)^2\left[(1-a)\frac{F_k(0)}{p^2}
                         +a\frac{F_k(1)}{(1-p)^2}\right]\ge0 .
\]
This includes intermediate success counts at arbitrary bank sizes. The total deficit is strictly positive if \(a\ne p\). The weak inequality extends to \(p=0,1\) by continuity. The claim permits an arbitrary change of the named probability and requires the other probabilities to coincide.

**Homogeneous calibration on a stratum.** With common probability \(t\), summing the weighted all-hit log probabilities gives \(\sum_{s=0}^{2m}\binom{m+s-1}{s}t^m(1-t)^s\), the probability that the \(m\)-th hit occurs by trial \(3m\). Thus the full tail equals the stopped mean for every \(t\). On expanding the difference over labelled outcomes, the coefficients of \(t^k(1-t)^{3m-k}\) vanish individually, by division by \((1-t)^{3m}\) and uniqueness of polynomial coefficients in the odds. Under the homogeneous law given \(S=k\), weighting by \(Z\) therefore defines a probability measure for every \(k\ge m\). The same calibration applies to a bank of \(m-1\) tasks. On strata below its threshold the smaller score vanishes.

**Endpoints and interpolation.** At \(a=0\) the stopped score is zero. At \(a=1\) delete the certain task. Its wait is zero, and its three actual successes leave \(S'=k-3\) on the remaining tasks. Their old score dominates the score in the enlarged bank pointwise: inserting a uniformly located bar in a uniform stars-and-bars word produces a uniform composition with one extra part and can only split an existing part. Thus at the same wait the probability of fitting the cap increases and its reciprocal decreases. The [certain-task comparison](certain-batches.md) gives details. Stratum calibration in the remaining bank now yields \(F_k(1)\ge0\), including when \(k-3<m-1\). Out-of-support counts contribute zero.

The multivariate stratum deficit is a symmetric polynomial in the \(m\) task probabilities. It vanishes on the entire diagonal, so the sum of its partial derivatives there vanishes. Symmetry makes those partial derivatives equal. Hence \(F_k(p)=F'_k(p)=0\). The named task contributes three Bernoulli factors, so the degree in \(a\) is at most three. After dividing out \((a-p)^2\), the remaining affine polynomial is fixed by its endpoint values. This gives the stated identity. For strictness after summation, with \(Y\sim\operatorname{Bin}(3(m-1),p)\), the two total endpoint deficits obey
\[
 \sum_{k\ge m}F_k(0)=\Pr(Y\ge m)>0,\qquad
 \sum_{k\ge m}F_k(1)\ge\Pr(m-3\le Y<m-1)>0 .
\]
Both inequalities are valid also for \(m=2\). This proves strictness even at either endpoint of \(a\).

**A comparison for all convex functions.** Under the homogeneous law conditional on \(S=k\), let \(R\) count successes on the named task, and let \(d_j=\Pr(R=j\mid S=k)-E[Z\,1_{\{R=j\}}\mid S=k]\). Both laws have total mass one. Both assign mean \(k/m\) to \(R\), by exchangeability and the fixed sum. We have \(d_0\ge0\) because the weighted law requires every task to hit. Also \(d_3\ge0\): given three hits on this task the remaining bank is homogeneous on count \(k-3\), and the preceding deletion comparison bounds the conditional mean of the enlarged score by one. If the event is empty both masses are zero.

For every function \(f\) on \(\{0,1,2,3\}\), the two zero-sum identities give exactly
\[
 \sum_{j=0}^3 d_j f(j)=d_0\,[f(2)-2f(1)+f(0)]
                       +d_3\,[f(3)-2f(2)+f(1)].
\]
Thus score weighting decreases the expectation of every convex function of the named count on every such stratum, preserving its mean. An alternative derivation of the bias inequality uses the likelihood ratio for replacing the named probability. Up to a positive constant it is \(t^R\) with \(t=a(1-p)/(p(1-a))>0\), a convex function of the count. Continuity covers \(a=0,1\).

**Where the argument stops.** At four attempts the quotient of the stratum deficit by \((a-p)^2\) can be quadratic. Nonnegative endpoints alone do not certify it: the abstract quotient \((a-1/2)^2-1/16\) is an example. This is a limitation of interpolation, not a score counterexample. For the convex-order argument at four attempts there is precisely one additional condition, the central hinge \(E[(R-2)_+\mid S=k]\ge E[Z(R-2)_+\mid S=k]\); the other two hinges follow from the endpoint masses as above. This identifies a single falsifiable test at the next cap. General heterogeneous banks with several arbitrary probabilities at cap three also remain open beyond existing certificates.

**A failed shortcut for the central hinge.** Deletion does not give a pointwise upper bound after conditioning the named task to have three hits out of four. For two tasks with four attempts, let the remaining task hit first on its fourth attempt. Its single-task score is one. The named task with exactly three successes has wait zero with probability three quarters and wait one with probability one quarter. The enlarged weights at waits three and four are one and five thirds, respectively. The conditional mean enlarged score is seven sixths. Any argument for the central hinge must allow compensation across outcomes or counts.

**Scope and checks.** The result applies to the pooled count of independent attempts. Its expected-score direction would matter when deciding whether heterogeneous task difficulty can inflate this specific benchmark score. It does not establish an empirical size of bias on a deployed model or apply directly to per-task pass@k. The [finite transport certificates](profile-transport.md) already cover arbitrary banks through 16 tasks at cap three; the proof here covers an unbounded bank size on the single-replacement family. The associated program checks exact stratum deficits using suffix binomial laws and compares the small designs to direct enumeration of all full trial outcomes. This note is subsequent to the reviewed manuscript.
