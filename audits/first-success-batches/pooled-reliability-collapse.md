# A pooled target approaching one while its stopped score approaches zero

The full target is the probability of at least $m$ successes across $mn$ potential independent trials. Successes on different attempts of the same task all count. This is a pooled reliability target. Each of the $m$ batches has its own success probability $p_i$ and permits $n$ attempts, but only the first hit or exhaustion is recorded. Use the canonical score defined in the first-success manuscript. Fix the cap $n\ge2$ while the number of batches grows.

Let $\bar p_m$ and $g_m$ be the arithmetic and geometric means of the batch probabilities, and set $a_n=(n-1)^{n-1}/n^n$. If $\liminf n\bar p_m>1$ and $\limsup g_m<a_n$, the full target tends to one while the expected stopped score tends to zero. The difference tends to one, the largest possible deficit for a nonnegative score and a target probability. All individual probabilities can be fixed at interior values across the entire sequence.

**Proof.** The total number $S$ of potential successes has expectation $mn\bar p_m$ and variance at most $mn/4$. When the expectation exceeds $m$ by at least $\delta m$, Chebyshev gives $\Pr(S<m)\le n/(4m\delta^2)$. For the score, discard the failure factors from each wait-vector probability. Summing the weights leaves
$$
\mathbb E Z \le \binom{mn}{m}\prod_i p_i
\le (g_m/a_n)^m .
$$
The second bound follows because the probability of exactly $m$ hits in a binomial experiment with $mn$ trials and success probability $1/n$ is at most one. These bounds prove both limits. The assumptions suffice for this separation; they are not a characterization.

**One fixed pair of task difficulties.** Let $m$ be even, $n=3$, and take half the probabilities equal to $3/4$ and the others equal to $1/50$. The mean full count is $231m/200$. For the full probability use $z=3/4$. On $S\le m$, $z^S\ge z^m$. Independence thus yields
$$
\Pr(S<m)\le\left[\frac{16}{9}\left(\frac{2587}{3200}\right)^3\right]^{m/2},
\qquad
\mathbb E Z\le(2187/3200)^{m/2}.
$$
Both bases are strictly less than one. At $m=300$, for example, the first bound is below $10^{-3}$ and the second below $10^{-24}$. These are bounds on the two expectations under the specified independent synthetic trial laws, not measurements from an AI service. The target can be met by repeated successes on the easier tasks, while the stopped score is zero whenever any task exhausts its trials. Homogeneous calibration does not protect this pooled comparison against fixed differences in task difficulty.

The companion script independently constructs both count distributions with integer convolutions, bounds rounding of the score summation term by term, and verifies the displayed rational inequalities. This result is part of the first-success research line and postdates the manuscript's exact-PDF review.
