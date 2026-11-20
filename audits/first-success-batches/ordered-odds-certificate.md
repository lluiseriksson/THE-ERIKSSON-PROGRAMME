# Bias certificates for three and four batches

For three batches with equal caps 3, 4 or 5, and for four batches with cap 3, the expected homogeneous stopped score is strictly smaller than the true full-budget tail whenever the independent batch probabilities are unequal and interior. This statement covers every real probability vector in these dimensions. The weak inequality on the closed cube follows by continuity.

Write $m$ for the number of batches and $n$ for the cap. Sort the odds $\theta_i=p_i/(1-p_i)$ in nondecreasing order. Put $g_1=\theta_1$ and $g_i=\theta_i-\theta_{i-1}$ otherwise. The full-budget target is the chance of at least $m$ successes in $mn$ independent trials. The stopped score is zero if a batch has no hit and otherwise is $w_s=\binom{m+s-1}{m-1}/A_s$ where $s$ is the total failures preceding the hits. Here $A_s$ counts ordered wait vectors in $\{0,\ldots,n-1\}^m$ with sum $s$.

After multiplication by $D=\prod_i(1+\theta_i)^n$, the full-budget probability minus the mean stopped score equals
$$
\sum_{\substack{0\le k_i\le n\\ \sum_i k_i\ge m}}\prod_i \binom{n}{k_i}\theta_i^{k_i}
-\sum_{0\le u_i<n}w_{\sum_i u_i}\prod_i\theta_i(1+\theta_i)^{n-1-u_i}.
$$
The first term groups full outcomes by success counts. The second groups stopped outcomes by their waits. Substitute $\theta_i=g_1+\cdots+g_i$ and clear the denominators of the $w_s$. The resulting polynomial is given as exact integer monomial coefficients in ordered.json. Entries omitted from the sparse array are zero. In the following table every surviving coefficient is positive and every monomial involves at least one gap $g_i$ for $i>1$.

| Batches | Cap | Positive scaling factor | Surviving terms | Smallest coefficient |
| --- | --- | --- | --- | --- |
| 3 | 3 | 14 | 52 | 14 |
| 3 | 4 | 20 | 117 | 20 |
| 3 | 5 | 114 | 217 | 114 |
| 4 | 3 | 380 | 490 | 380 |

The sign follows on the sorted cone because all gaps are nonnegative. For each $i>1$ at least one positive monomial uses only $g_i$ and possibly $g_1$, with positive exponent on $g_i$. In the interior $g_1>0$. Hence any positive gap suffices for strictness. For example, for four batches and cap three the last gap has the witness $3420g_1g_4^3$. Equality on the diagonal follows by setting all gaps except $g_1$ to zero.

The generator ordered_odds.py constructs the two generating polynomials directly from the two observation laws. It expands each substitution by integer convolution and compares its evaluation against both original probability laws at three choices of odds per dimension. The case-by-case polynomial identities are finite algebraic certificates. A sign proof for general dimensions remains open. These calculations supplement the first-success manuscript and were performed after the exact-PDF assessment.
