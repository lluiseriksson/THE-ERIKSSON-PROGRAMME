# Observed work and the price of allowing different success rates

Supplement to [PR 334](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/pull/334). The frozen paper covers the common-probability minimum variance and a nonnegativity obstruction. These additional results have their own source revision and have not received the PDF's assessment.

## Fixing expected work changes the allocation problem

For a fixed design let W be its expected number of observed trials and V the minimum variance in the nonnegative unbiased class. Their product is a useful asymptotic comparison for averaging independent repetitions at the same expected total work. It measures neither parallel wall time nor worst-case cost.

At T=10, m=4, p=1/8, changing caps (2,2,3,3) to (2,2,2,4) increases V and reduces W enough to make WV smaller. The certificate lists the exact fractions for all eligible partitions. Thus the variance-optimal allocation in the paper need not optimize work times variance.

**A whole regime.** Fix 0<p<1 and a positive surplus L=T−m. When m is sufficiently large at fixed L, concentrating the entire surplus in one cap (L+1,1,…,1) minimizes WV uniquely up to relabeling. For L≥2 this is the opposite of balancing at fixed maximum work. To prove it, write eᵢ=nᵢ−1, q=1−p and u(e)=Σᵢ(q+⋯+q^{eᵢ}), so W=m+u(e). The nonzero extras form one of finitely many partitions of L. Write Cⱼ=binom(m+j−1,j), and let Aⱼ be the coefficient of xʲ in the product of (1+x+⋯+x^{eᵢ}). After division by p^m, V has the common term
     
    Hₘ=C_L² q^L − p^m (Σⱼ Cⱼqʲ)²
     
and a pattern-dependent remainder O(m^{2L−2}), uniformly over the finite patterns. This follows from A_L=1. The common term is asymptotic to m^{2L} q^L/(L!)². In the difference between two products, divided by p^m, the leading term is [u(e)−u(f)]Hₘ and the error is O(m^{2L−1}). Combining two positive extras into a single cap strictly decreases u, since q+⋯+q^{a+b} is strictly less than the sum of the separate two geometric sums. Thus the concentrated allocation wins against every other pattern eventually. The threshold in m can depend on L and p.

## Heterogeneous attempts: signed corrections grow exponentially

Let the i-th batch have its own arbitrary probability pᵢ, constant across that batch. At cap n its record is a failure, or a first success after u failures, 0≤u<n. A real-valued score with finite conditional means is uniquely identified at the level of its conditional means by the target polynomial. The one-batch record probabilities qⁿ, (1−q)qᵘ are a basis of polynomials in q=1−p through degree n: evaluating a putative linear dependence at q=1 removes the first coefficient, and dividing the remaining polynomial by 1−q removes the rest. Their tensor products form a basis for independent batches. A deterministic unbiased score thus exists even where nonnegative estimation is impossible.

For the probability generating function of the full success count, the unique score of a failed batch is the polynomial 1. The score for a success after u failures is
     
    Hᵤ(z) = Σⱼ₌₀ᵘ binom(n,j) z^{n−j}(1−z)ʲ .
     
Indeed qⁿ+(1−q)ΣᵤqᵘHᵤ(z)=[z+(1−z)q]ⁿ by telescoping. Multiply across batches and sum the coefficients of zʲ for j≥m to obtain the unique mean score for the full threshold. Individual coefficients can have either sign. For example, if all batches except j succeed only on their last allowed trial and batch j fails, this threshold score is 1−∏ᵢ≠ⱼ nᵢ: each last success contributes 1−(1−z)^{nᵢ}, and the lowest degree of the product is m−1.

**Exact exponential rate for two-attempt caps.** For m batches of two trials, let Mₘ⁺ be the largest conditional mean score and Mₘ⁻ the absolute value of the most negative one. Both have m-th root tending to 1+√2. With a immediate successes, b second-attempt successes and the rest failed, the record polynomial is z^{2a+b}(2−z)^b. Write d=m−2a−b. If d≤0 the score is one. If d>b it is zero. Otherwise it is
     
    S = Σⱼ₌dᵇ (−1)ʲ binom(b,j) 2^{b−j}.
     
The integral Taylor remainder at z=1 gives |S|=d binom(b,d)∫₀¹(1−t)^{d−1}(2−t)^{b−d}dt, with sign (−1)^d. Write L(b,d)=binom(b,d)2^{b−d}. Then |S|≤L(b,d), and |S|≥L(b,d)/(8b) by integrating from 0 to 1/(2b). On that interval (1−t)^{d−1}≥1/2 and (1−t/2)^{b−d}≥1/2 by Bernoulli's inequality.

The sum of L(b,d) over b+d=r, including d=0, is the coefficient Pᵣ of 1/(1−2x−x²). Thus Pᵣ grows proportionally to (1+√2)^r. Because b+d=m−2a≤m, all magnitudes have the same exponential upper bound. For the lower bound set a=0. The signed sum over b+d=m is the coefficient of 1/(1−2x+x²), namely m+1. Hence both the even and odd d sums of L(b,d) have growth rate 1+√2, even after dropping the d=0 term 2^m. Each sum has at most m+1 terms. Select its largest term and use the integral lower bound above. The polynomial factors lost do not change the m-th root. This proves the claim for both signs. Auxiliary randomization cannot remove these forced conditional means.

These worst-case statements concern the range required for exact unbiased reporting for all batch-specific probabilities. They do not estimate how often extreme scores occur in an actual benchmark. The exact signed coefficients were checked through 80 batches. Small cases were also checked by direct expectation at different batch probabilities. The common-probability work comparisons use exact rational arithmetic.
