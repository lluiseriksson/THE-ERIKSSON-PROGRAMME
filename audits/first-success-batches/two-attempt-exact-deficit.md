# Exact deficit as a positive sum for arbitrary finite two-attempt designs

The sign theorem and its conditional occupancy argument already appear in the programme's earlier two-attempt-bias.md. The quantitative result here computes the size of the bias. It gives an exact sum of pairwise squared probability differences with nonnegative weights, including at boundary probabilities.

For \(m\ge2\) independent tasks, let task \(i\) have two independent potential attempts of success probability \(p_i\), and set \(q_i=1-p_i\). Write \(S\) for the total full successes and \(Z\) for the calibrated canonical first-hit score. For \(m\le k\le2m\) let \(J=\lfloor(2m-k)/2\rfloor\). At total \(k\), the count profile with \(t\) zeros has \(h_t=k-m+t\) twos and \(s_t=2m-k-2t\) ones. It represents \(N_{k,t}=m!2^{s_t}/(t!h_t!s_t!)\) labelled outcomes. For a pair \(i<l\) and \(1\le j\le J\), let \(A_{k,j}^{il}\) be the uniform assignment average of
\[
 \prod_{u\ne i,l}p_u^{r_u}q_u^{2-r_u}
\]
over permutations of \(j-1\) zeros, \(h_j-1\) twos, and \(s_j\) ones on the other \(m-2\) tasks. An empty product is one. Then the exact contribution from \(S=k\) to the target minus the score is
\[
 \frac1{2\binom m2}\sum_{i<l}(p_i-p_l)^2
 \sum_{j=1}^J A_{k,j}^{il}\sum_{t=j}^J N_{k,t}.
\]
Summing over \(k\) gives the full deficit. Thus a design's bias is evaluated stratum by stratum without enumerating the stopped logs.

**Proof.** For interior probabilities remove \(D=\prod q_i^2\) and write \(\theta_i=p_i/q_i\). Let \(M_j\) denote the permutation average of the monomial in the odds with the \(j\)-zero profile at the given \(k\). The conditional comparison in the earlier sign proof gives the unnormalized deficit divided by \(D\) as \(\sum_t N_{k,t}(M_t-M_0)\). Telescope and exchange finite sums. To compute \(M_j-M_{j-1}\), assign its exponents uniformly, pick a two and a zero uniformly from their respective slots, and balance them to ones. The resulting assignment is uniform for its new profile by permutation symmetry. The chosen unordered pair is uniform on \(\binom m2\) choices and its two orientations have equal probability. Conditional on the unordered pair, the remaining exponents are uniformly permuted with exactly the counts defining \(A\). Averaging the two orientations gives \((\theta_i-\theta_l)^2/2\) times the remaining product. Multiplication by \(D\) changes this to \((p_i-p_l)^2/2\) times the remaining product in the definition of \(A\). Continuity gives the identity on the closed cube.

**A simpler computable bound.** Retain only contributions of original profiles with exactly one zero, for all \(k\). Assign this zero a partner chosen uniformly from its \(h_1\) doubled sites. If the set \(B\) of other doubled sites has size \(b\), the weight on the balanced pair is \(1/(b+1)\). Single-success remaining slots each admit two labelled outcomes. Pairing the two orientations and summing \(B\) therefore gives
\[
 \Pr(S\ge m)-EZ\ \ge\
 \sum_{i<l}(p_i-p_l)^2\int_0^1
 \prod_{u\ne i,l}\left(2p_uq_u+x p_u^2\right)\,dx .
\]
The integral implements \(1/(b+1)=\int_0^1x^b\,dx\). Dropping all terms except \(B=\emptyset\) recovers the critical-stratum quadratic bound. The integral expression is exact for \(m=2,3\): no stratum \(k\ge m\) then admits two empty tasks. In particular for three tasks the weight for pair \(i,l\) equals \(2p_u-3p_u^2/2\) for the remaining task \(u\). In the interior with \(m\ge4\) and unequal probabilities the bound is strict: already \(k=m,t=2\) has positive coefficient and its first balancing step is strictly positive on averaging assignments.

The general finite sign for larger common caps remains open. The source identity, labelled-outcome comparison and reproducible rational checks are part of the first-success manuscript dossier. No priority claim is made about inequalities for symmetric means; the classical ingredient is [Muirhead's inequality](https://doi.org/10.1017/S001309150003460X).
