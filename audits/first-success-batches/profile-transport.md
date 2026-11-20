# Comparing stopped and full scores one success stratum at a time

Let \(m\) independent tasks each have \(n\) independent potential Bernoulli trials, with fixed probability \(p_i\) on task \(i\). The full count is \(S\). The first-success score \(Z\) vanishes unless all tasks hit, and then equals \(w_s=\binom{m+s-1}{s}/[z^s](1+\dots+z^{n-1})^m\), where \(s\) is the total number of failures preceding first hits. The following results concern \(E[Z1_{\{S=k\}}]\), a contribution evaluated on the underlying full experiment. The full count need not be present in the stopped log.

**Finite theorem.** For all \(p_i\in[0,1]\), \(E[Z1_{\{S=k\}}]\le\Pr(S=k)\) for every \(k\ge m\) in all the following designs:

| Common attempt cap | Number of tasks |
|---|---|
| 3 | 2 through 16 |
| 4 | 2 through 10 |
| 5 | 2 through 7 |
| 6 | 2 through 5 |

Consequently \(E Z\le\Pr(S\ge m)\) for each of these designs, strictly for unequal interior probabilities. The 644 stratum certificates cover the continuum of probability vectors. They contain 8,352 positive transfers.

**Certificate identity.** Let \(r\) be an unordered profile of \(m\) task success counts with sum \(k\) and entries in \([0,n]\). Let \(d_r\) count its distinct permutations. The number of full labelled outcomes in its orbit is \(N_r=d_r\prod_i\binom{n}{r_i}\). The sum \(W_r\) of their stopped scores is zero if some entry vanishes. Otherwise it is
\[
 W_r=d_r\sum_s w_s[z^s]\prod_i\sum_{u=0}^{n-r_i}\binom{n-u-1}{r_i-1}z^u .
\]
Here the first success fixes one slot, leaving \(r_i-1\) later successes. Remove the common probability factor \(D=\prod_i(1-p_i)^n\) for interior parameters and let \(M_r\) denote the normalized symmetric monomial in the task odds. The stratum deficit divided by \(D\) equals \(\sum_r(N_r-W_r)M_r\). Homogeneous unbiasedness by total-degree coefficients implies \(\sum_r(N_r-W_r)=0\).

Seek a flow from positive to negative coefficients along pairs \(r\succeq t\) in majorization order. Clearing denominators requires only the common multiple of the coefficients of \((1+\dots+z^{n-1})^m\). With exact row and column sums the deficit is a nonnegative weighted sum of \(M_r-M_t\) by [Muirhead's inequality](https://doi.org/10.1017/S001309150003460X). Polynomial continuity covers the boundary. In the critical stratum \(k=m\) the one all-positive profile consists entirely of ones. It receives a strictly positive contribution from the orbit with one two and one zero whenever two interior odds differ, giving strictness for the sum. For \(k<m\) both contributions to the tail comparison vanish.

The archive profile-transport-certificates.zip stores the witnesses by cap and number of tasks. The producer recomputes the margins by a second coefficient formula using inclusion-exclusion, checks the true ordering via prefix sums on ascending profiles, and verifies each edge as an integer. It checks every marginal balance exactly. A flow is sufficient; an infeasible flow by itself would only defeat that certificate, not establish overestimation. The finite result does not extrapolate to untested dimensions.
