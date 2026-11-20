# Two batches with arbitrary common depth

Consider independent Bernoulli trials with success probabilities $p_1,p_2$ within two respective batches. Each permits $n$ attempts and reveals only the first success or exhaustion. Write $q_i=1-p_i$. The target is the chance of at least two successes among all $2n$ potential trials. Score zero unless both batches hit. If both hit after $u,v$ failures, put $s=u+v$ and score $(s+1)/A_s$, where $A_s$ counts the ordered pairs in $[0,n-1]^2$ summing to $s$.

**Proposition.** For every common depth $n\ge2$, the mean score is at most the true target, with equality precisely at $p_1=p_2$. At depth one there is equality for all probabilities.

**Proof.** The event that both batches hit contributes its probability to both sides. On its complement the target can occur only when one batch fails and the other gets at least two successes. The probability that the latter's second success occurs after exactly $d$ failures is $(d+1)p_i^2 q_i^d$, for $0\le d\le n-2$.

The score exceeds one only at $s=n+d$, where $A_s=n-1-d$ and its excess is $2(d+1)/A_s$. Subtraction gives the following exact difference between target and mean score, with the sum over $d=0,\ldots,n-2$:
$$
\sum_d(d+1)\left[p_2^2X+p_1^2Y-\frac{2p_1p_2}{n-1-d}
\sum_{u=d+1}^{n-1}q_1^u q_2^{n+d-u}\right],\qquad
X=q_1^n q_2^d,\quad Y=q_1^d q_2^n.
$$

Relabel so $q_1\ge q_2$, hence $p_2\ge p_1$ and $X\ge Y$. Each paired pair of middle monomials has sum at most $X+Y$. To see this, for $0<q_2\le q_1$ divide throughout by $q_1^d q_2^n$, set $r=q_1/q_2$, $j=u-d$, and $h=n-d$. The difference is $(r^j-1)(r^{h-j}-1)\ge0$. The boundary follows by continuity with the convention $q^0=1$. Thus the bracket is at least $(p_2-p_1)(p_2X-p_1Y)$. For distinct probabilities the $d=0$ term is strictly positive, including at the endpoints. At equal probabilities all inequalities are equalities. For $n=1$ the observed data contain both trials in full.

This proposition determines the direction of the bias for any two equally capped batches. Extending it to three or more batches with depth at least three requires a separate argument. This is a supplement to the first-success manuscript and has no separate assessment or publication status.

The exact rational audit independently calculates the full target and stopped score from their separate laws. For two batches it checks the displayed difference at 450 depth/probability configurations. Another 245 configurations with three or four batches supply finite evidence only. Four heterogeneous boundary cases at four batches of depth three have zero target and zero mean score: even the full budget cannot deliver four successes when only one batch can succeed.
