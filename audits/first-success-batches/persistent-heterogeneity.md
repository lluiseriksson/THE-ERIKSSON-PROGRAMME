# Persistent heterogeneity drives the stopped score below the full tail on a relative scale

For each row of a triangular array, let $m$ independent batches each allow $n\ge2$ independent Bernoulli trials. The common cap $n$ is fixed across rows; the batch probabilities $p_i$ may vary arbitrarily with $m$. Let $P_m=\Pr(S\ge m)$ for the number $S$ of successes in all $T=mn$ potential trials. Let $Z_m$ be the canonical homogeneous score on the first-success logs. It is zero unless all batches hit; on such records its value is $C_s/A_s$, where $s$ is the total number of observed failures, $C_s=\binom{m+s-1}{m-1}$ and $A_s=[z^s]U(z)^m$, $U(z)=1+z+\cdots+z^{n-1}$. Define $V_m=m^{-1}\sum_i(p_i-\bar p)^2$.

**Theorem.** Given $0<a\le b<1$, there is $c=c(n,a,b)>0$ such that for all $p_i\in[a,b]$,
$$
\frac{\mathbb E Z_m}{P_m}\ \le\ (mn+1)^5 \exp(-c m V_m).
$$
In particular, any persistent positive variance gives exponential decay of the ratio even if the full tail itself is rare. The conclusion also holds as convergence to zero if $mV_m/\log(m+1)\to\infty$. When $\liminf n\bar p>1$ and $\liminf V_m>0$, $P_m\to1$ and $\mathbb E Z_m\to0$. Two fixed interior probabilities of arbitrarily small positive separation, in fixed positive proportions and with average above $1/n$, suffice. The geometric-mean threshold from the elementary sufficient condition is unnecessary. The bound need not be informative at small $m$ and does not determine the sign for every finite design.

**1. An atom bound.** A log-concave mass function on $\{0,\ldots,L\}$ with contiguous support and integer mean $s$ assigns mass at least $(L+1)^{-2}$ to $s$. Both closed half intervals meeting at $s$ have mass at least $1/(L+1)$: otherwise the integer gap to the opposite side prevents the mean from being $s$. On each side some atom therefore has mass at least $(L+1)^{-2}$, and unimodality puts the intervening atom above their minimum. We use closure of discrete log-concavity under independent sums, as in Hoggar's theorem (Johnson and Goldschmidt, Theorem 1.4, cited below).

**2. A coefficient bound.** Write $q_i=1-p_i$, $L=m(n-1)$. The contribution to $\mathbb E Z_m$ from wait $s$ is
$$
C_s\,\prod_i(1-q_i)\frac{[z^s]\prod_i U(q_i z)}{[z^s]U(z)^m}.
$$
For $0<s<L$, set $\rho=s/m$, $v=\rho/(1+\rho)$ and choose $x>0$ so that $xU'(x)/U(x)=\rho$. The left side increases continuously from $0$ to $n-1$ since its derivative in $\log x$ is the positive variance of the distribution proportional to $x^j$, $0\le j<n$. The denominator coefficient is at least $U(x)^m x^{-s}/(L+1)^2$ by applying step 1 to a sum of $m$ independent such variables. Positivity gives $C_s\le(1-v)^{-m}v^{-s}$ and the numerator coefficient is at most $(x/v)^{-s}\prod_i U(q_i x/v)$. The factors in $s$ cancel. The contribution is at most $(L+1)^2\prod_i R_v(q_i)$, where
$$
R_v(q)=\frac{(1-q)U(c_v q)}{(1-v)U(c_v v)},\qquad c_v=x/v .
$$

**3. A strictly peaked profile.** One has $c_v>1$: truncating a geometric series at $n-1$ strictly decreases its mean when $x<1$, and when $x\ge1$ the inequality is immediate. For $c>1$ the polynomial
$$
F_c(q)=(1-q)U(cq)=1+(c-1)\sum_{j=1}^{n-1}c^{j-1}q^j-c^{n-1}q^n
$$
has a unique, nondegenerate interior maximum when $c=c_v$. In fact $F_{c_v}'(v)=0$ by the defining mean equation, and $F_c'(q)/q^{n-1}$ is strictly decreasing on $(0,1)$, with negative derivative there. Thus $R_v\le1$, with equality only at $q=v$. The endpoint profiles at $v=0$ and $v=(n-1)/n$ are respectively $1-q^n$ and $(1-q)q^{n-1}/[(1-v)v^{n-1}]$. These follow by $x\downarrow0$ (so $x/v\to1$) and $x\to\infty$, including the first two $q$ derivatives on compact interior $q$-intervals. The same bound on the endpoint contributions follows directly for $s=0$ and by taking $x\to\infty$ in the leading-coefficient bound for $s=L$, with $v=(n-1)/n$.

For $q$ in a fixed compact subinterval of $(0,1)$, compactness and strictness give $R_v(q)\le\exp[-c_0(q-v)^2]$ uniformly for $0\le v\le(n-1)/n$. Indeed $-\log R_v(q)/(q-v)^2$ extends on the interior diagonal by $-F_{c_v}''(v)/(2F_{c_v}(v))>0$. The right endpoint has the same strictly negative log-curvature at its maximum, and the left endpoint $q=v=0$ is outside the prescribed $q$-interval. Summing the contribution bound over $s$, and using $\sum_i(q_i-v)^2\ge mV_m$, gives $\mathbb E Z_m\le (L+1)^3\exp(-c_0mV_m)$.

**4. Transfer to a rare full tail.** If $\mathbb E S\ge m$, then $P_m\ge1/(T+1)$ by the integer-gap argument. Otherwise tilt all trial odds by the same factor $\lambda>1$, chosen so that the tilted mean of $S$ is exactly $m$. The new batch probability is $h_\lambda(p)=\lambda p/(1-p+\lambda p)$. Since $p_i\ge a$, the required factor is at most $\max(1,(1-a)/(a(n-1)))$. All tilted probabilities stay in a common compact interior interval, and $h_\lambda'$ is uniformly bounded below by a positive constant there. The pairwise formula for variance then gives $V_m^\lambda\ge d^2V_m$ with $d>0$ independent of the row. The likelihood ratio of the original full trials relative to the tilted trials is $K\lambda^{-S}$ for a constant $K$. Whenever $Z_m>0$ we have $S\ge m$ on every full completion. Therefore
$$
\frac{\mathbb E Z_m}{P_m}
\le\frac{\mathbb E_\lambda Z_m}{\Pr_\lambda(S=m)} .
$$
Step 1 for the sum of tilted Bernoulli trials gives $\Pr_\lambda(S=m)\ge(T+1)^{-2}$. Apply step 3 to the tilted row. Bounding $L+1$ by $T+1$ proves the theorem after taking the smaller exponent constant from the two cases. Finally, the variance of the original total is at most $T/4$, so the stated above-threshold limit follows by Chebyshev.

**Endpoint corollary for absolute error.** For every \(v_0>0\) there is \(\eta(n,v_0)>0\) such that \(\mathbb E Z_m\le (L+1)^3\exp(-\eta m)\) whenever \(V_m\ge v_0\), now permitting every \(p_i\in[0,1]\). Indeed the normalized polynomials \(R_v(q)\) extend jointly continuously to the entire closed rectangle, by convergence of their finitely many normalized coefficients at both ends of the parameter range. Their maximum is unique at \(q=v\), including the endpoint profiles. For each \(v\), the empirical mean of \((q_i-v)^2\) is at least \(v_0\); since all squared distances are at most one, a fraction at least \(v_0/2\) have distance at least \(\sqrt{v_0/2}\). On this compact off-diagonal set the supremum of \(R_v(q)\) is strictly below one. Substitution in step 3 proves the bound, also for batches that always hit or always miss. When \(\mathbb E S\ge m\), dividing by \(P_m\ge1/(T+1)\) gives the same exponential decay on the relative scale. For a rare full tail the uniform interior assumption in step 4 continues to apply.

**Scope and provenance.** This argument concerns a pooled count which credits repeated successes on one task. It does not change the definition of per-task pass@$k$. The coefficient identity is from the programme manuscript. The cited convolution theorem is a classical ingredient. The new application and the finite checks are recorded together; no bibliographic priority or independent peer review is asserted. [Johnson and Goldschmidt, Preservation of log-concavity on summation](https://www.numdam.org/item/10.1051/ps%3A2006008.pdf).
