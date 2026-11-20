# The rare-success region and a heterogeneity certificate

Use the notation $m,n,T,P,Z$ of uniform-high-reliability.md, but here $t=\max_i p_i$, $C=\binom{T}{m}$, $h=\binom n2 n^{m-2}$ and $c=h/C$. For each fixed $m,n\ge2$ there is an explicit $\eta>0$ such that $P>\mathbb E Z$ for every nonconstant interior success-probability vector with $t\le\eta$. Equal probabilities give exact equality. Both this and the high-reliability theorem compare the score with the latent full-budget target at the same batch probabilities.

**Certificate at arbitrary success rates.** Suppose all $p_i>0$. Write $S=e_m(p_1,\ldots,p_1,\ldots,p_m,\ldots,p_m)$ with each variable repeated $n$ times and $M=C\prod_i p_i$. The elementary symmetric polynomial sums the success products of the $m$-subsets of $T$ labelled trials. The geometric mean of their products is $\prod_i p_i$, since each batch occurs once on average. In fact
$$
\frac SM\ \ge\ 1+c\sum_{i<j}\frac{(p_i-p_j)^2}{p_i p_j}.
$$
To see the stronger bound, divide each subset product by $\prod_i p_i$ and call the result $v$. The sum of $\log v$ over all subsets is zero. In the sum of $v-1-\log v\ge0$ keep only subsets taking two trials from batch $i$, none from batch $j$, and one from every other batch. For each pair there are $h$ of each orientation. The normalized products are $p_i/p_j$ and its reciprocal. The retained sets from different ordered pairs are disjoint. This proves the bound.

The probability of exactly $m$ successes is at least $(1-t)^{T-m} S$. The stopped expectation is at most $M$ by bounding every failure factor by one and summing the score over wait vectors. In particular $P>\mathbb E Z$ whenever
$$
(1-t)^{T-m}\left[1+c\sum_{i<j}(p_i-p_j)^2/(p_i p_j)\right]>1.
$$
For $0<t<1$ this can certify the sign at considerable heterogeneity without expanding any polynomials. For zero probabilities, $\mathbb E Z=0$ directly. Then $P>0$ exactly when at least $m$ potential trials have positive success probability.

**Uniform sign even at arbitrarily small contrasts.** Normalize $x_i=p_i/t$, $y=\min_i x_i$. If $0<y\le1/2$, the sum of squared contrasts in the certificate is at least $(1-y)^2/y\ge1/2$. Thus the sign is strict for $t\le1-(1+c/4)^{-1/(T-m)}$. This case includes sequences approaching a face where the degree-$m$ coefficient alone has no uniform absolute lower bound.

For $y\ge1/2$, in the success variables the degree-$m$ term of $D=P-\mathbb E Z$ is $L=S(x)-M(x)$. Indeed, at lowest order only exactly $m$ full successes contribute, and the stopped score is multiplied by one success in every batch. There are no terms of lower degree. The strengthened bound on $S/M$ gives $L\ge H(1-y)^2$ for $H=2^{-m}h$. The coefficient norm of $D$ in the success variables is at most $B'=3^T+2^{T-m}C$: each stopped wait term has a prefactor $\prod p_i$ and at most $T-m$ factors of $1-p_i$. The same diagonal Taylor argument as in the high-reliability proof gives
$$
D(tx)/t^m\ \ge\ \left[H-\tfrac12 t T(T-1)B'\right](1-y)^2 .
$$
Taking $\eta$ to be the smaller of $1-(1+c/4)^{-1/(T-m)}$ and $H/[T(T-1)B']$ proves the claim. The middle range between the two uniform theorems remains open for general designs. The numerical usefulness of the conservative uniform thresholds is distinct from the exact computable heterogeneity certificate.
