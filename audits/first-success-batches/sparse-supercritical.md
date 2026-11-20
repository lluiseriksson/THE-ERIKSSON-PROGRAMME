# A sparse exceptional set when the full target is almost certain

In the same capped Bernoulli model, suppose the background success probability \(p\in(1/n,1)\) and cap \(n\ge2\) are fixed. In a bank of \(m\) tasks replace \(r=r_m\ge1\), \(r=o(m)\), by tasks with arbitrary failure probabilities \(x_1,\ldots,x_r\). The full pooled target \(P\) tends to one exponentially fast, uniformly in the replacements: the remaining \(n(m-r)\) Bernoulli-\(p\) trials alone exceed \(m\) successes in expectation by order \(m\), and the lower-tail Chernoff bound applies.

Write \(q=1-p\), \(U(z)=1+\cdots+z^{n-1}\), and let \(z>0\) solve \(zU'(z)/U(z)=q/p\). This is possible because the mean runs strictly increasingly from zero to \(n-1\). Define
\[
 R(x)=\frac{1-x}{p}\frac{U(zx/q)}{U(z)}.
\]
Uniformly in the exceptional probabilities strictly below one,
\[
 \log(EZ/P)=\sum_{i=1}^r\log R(x_i)+o(r).
\]
The exponentially small factors \(1-x_i\) need no lower bound. A task with \(x_i=1\) makes \(EZ=0\) exactly. For bounded \(r\), the result is a multiplicative equivalent; for growing \(r\) its precision is logarithmic per exceptional task.

**Example.** At cap three and \(p=1/2\), \(z=1\). A single replacement with certain success has \(R(0)=2/3\). Its mean stopped score tends to two thirds even though the full target tends to one. If \(r\to\infty\) and \(r=o(m)\) such replacements are made, then \(\log(EZ/P)/r\to\log(2/3)\). Hence an arbitrarily slowly growing number of improvements can drive the mean score to zero, although the fraction of changed tasks and the variance of task probabilities both vanish. For example \(r=\lfloor\log\log m\rfloor\) eventually suffices. The [rare-tail and threshold-window formula](exceptional-tasks.md) describes the contrasting polynomial loss from a single certain replacement at smaller background success rates.

**Concentration under the score-weighted law.** As in the rare-tail proof, normalize the homogeneous log law by the weight \(Z/P_0\), with \(P_0\) the homogeneous full target. Its total wait is a sum of \(m\) geometric-\(p\) waits conditional on being at most \(m(n-1)\). Its normalized sum is within any fixed tolerance of \(q/p\) with exponentially high probability by the exponential moment bound for geometric waits. The conditioning event has probability tending to one.

Conditional on total wait \(s\), the log is a uniform capped composition of \(s\). Equivalently its coordinates are independent with probabilities \(z_s^j/U(z_s)\) on \(j=0,\ldots,n-1\), conditioned on sum \(s\), where \(z_s\) is chosen so their sum has mean \(s\) before conditioning. The conditioning event has probability at least \([m(n-1)+1]^{-2}\): the sum has contiguous log-concave mass function, and the closed half intervals touching its integer mean each carry at least \(1/[m(n-1)+1]\). On each side at least one atom has mass at least the square of that bound; unimodality bounds the atom between them from below. Log-concavity of such convolutions is classical. By the concentration inequality for independent bounded variables, each empirical frequency under the unconditioned categorical law is exponentially close in probability to its mean at fixed tolerance. Dividing by the polynomial atom bound preserves exponential concentration. By continuity of \(z_s\) as a function of \(s/m\) near \(q/p\), the empirical histogram under the score-weighted homogeneous law is exponentially concentrated, at every fixed tolerance, about \(\pi_j=z^j/U(z)\). All its components are strictly positive. [Johnson and Goldschmidt](https://doi.org/10.1051/ps:2006008).

**Named coordinates on a typical histogram.** Let \(\nu\) be its normalized frequencies. Conditional on the histogram, the named waits are sampled without replacement. Suppose \(\max_j|\nu_j-\pi_j|\le\epsilon<\min_j\pi_j/2\). For any specified ordered pattern of \(r\) waits, its probability under sampling without replacement differs multiplicatively from its probability under independent sampling from \(\pi\) by factors in
\[
 [\exp(-C\epsilon r-Cr^2/m),\ \exp(C\epsilon r+Cr^2/m)]
\]
for a constant depending only on the background and cap, at all sufficiently large \(m\). To check this, compare each successive conditional probability \((m\nu_j-\text{number of earlier draws of type }j)/(m-\text{number of earlier draws})\) with \(\pi_j\); all denominators are bounded below after normalization and the accumulated log error is as stated.

After factoring out \(\prod_i(1-x_i)/p\), the score likelihood ratio is the mean of \(\prod_i(x_i/q)^{u_i}\). All terms are nonnegative, also when \(x_i=0\) with \(0^0=1\). The pattern comparison applies term by term. The independent-product expectation lies between \(\pi_0^r\) and \(q^{-(n-1)r}\), uniformly in the \(x_i\). The exceptional-histogram contribution is at most \(\exp[-c_\epsilon m]q^{-(n-1)r}\), negligible relative to \(\pi_0^r\). Take logarithms, divide by \(r\), then let \(\epsilon\downarrow0\). Multiplication by the factored-out constants and \(P_0/P\to1\) gives the claim.

**Direction and a separate check.** \(R(x)\le1\) with equality only at \(x=q\). Indeed \((1-x)U(cx)\) with \(c=z/q>1\) has its unique maximum at \(q\): its derivative vanishes there by the mean identity and, after division by \(x^{n-1}\), is strictly decreasing on \(x>0\). To see \(z>q\), truncating the geometric weights at \(q\) strictly lowers the untruncated mean \(q/(1-q)\). In the two-attempt case \(\pi_0=1-q/p\), giving \(R(0)=(2p-1)/p^2\). The independent [beta integral](two-attempt-integral.md) gives the same single-replacement factor by concentration at \(u=1/(2p)\): the integrand relative to the homogeneous integral is \((1-u)/[p(1-up)]\). Both calculations give three quarters at \(p=2/3\).

This is a statement about the pooled independent-trial experiment. The log estimate alone does not resolve a smaller discrepancy when \(\sum_i-\log R(x_i)=o(r)\) and \(r\) is unbounded. This supplement is subsequent to the frozen PDF.
