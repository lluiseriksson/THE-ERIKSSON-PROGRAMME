# Where uniform allocation of surplus successes breaks down

Consider the [independent capped retry experiment](growing-exceptions.md). There are m tasks, each with the same fixed cap n >= 2. On the stratum S=m+h, let Q be the uniform law of full labelled strings weighted by the calibrated first-success score Z. Under Q every task has a hit. Let E_i be its additional hits, so that E sums to h and each entry is at most N=n-1. Use C(m,h)=binom(m+h-1,h) for the number of unrestricted weak compositions. A specified vector below is **labelled**, even when its probability is very small.

**Theorem.** For h=o(sqrt(m)), uniformly over all admissible vectors e,
\[
 C(m,h)\,Q(E=e)=1+O_n((h+1)^2/m).
\]
For fixed n >= 3 this range is sharp. Take h divisible by N with h/sqrt(m) tending to c>0. For a vector with h/N entries N and all others zero, the left side tends to exp(-n c^2). For a vector with h entries one it tends to one. In particular replacing C(m,h) by another scalar common to all admissible profiles cannot give uniform relative accuracy at that scale.

**Reduction to an urn.** Put T=mn. Under Q let R be the number of suffix slots after removing the initial misses and first hit of each task. Its mass at R is binom(T-R-1,m-1) binom(R,h)/binom(T,m+h). This follows by counting completions at each total wait. Equivalently R counts positions after the m-th hit in a uniform subset of m+h positions. Conditional on R the suffix lengths form a uniform weak composition of R capped at N, and the h extra hits occupy a uniform h-subset of those slots. [Stratum count and suffix law](near-threshold-strata.md).

Generate R colours from an urn with m colours and initial weight one per colour, adding one unit to each drawn colour. The ordered draws are exchangeable: a particular sequence with final counts v has probability equal to the product of the factorials v_i! divided by the rising factorial of m of order R. Hence all final count vectors are equally probable, and independent of the order given those counts. The first h draws represent a uniform subset. Write A for the event that all final counts are at most N. For any admissible e, the conditional profile probability times C(m,h) is exactly
\[
 D_R(e)=\Pr(A\mid E^{\rm urn}=e,R)/\Pr(A\mid R).
\]
Here the conditioning in the numerator specifies the counts after h draws in the unrestricted urn. The required density is the average of D_R(e) over the displayed Q law of R. The compound multinomial model is classical. The cap and the random suffix length enter through this conditional ratio. [Mosimann, 1962](https://doi.org/10.1093/biomet/49.1-2.65).

**Uniform error.** For R <= delta m and fixed small delta, the probability of all distinct colours in R draws is the product of (m-j)/(m+j) over 0 <= j < R. It bounds the denominator below by exp(-C R²/m). The probability of any repetition is at most C R²/m by a union bound. After an admissible history e, a sufficient condition for A is that every new draw uses a previously unseen colour. After j new draws the used colours together have weight at most 2(h+j). Another union bound yields failure probability at most C R²/m. Therefore
\[
 |D_R(e)-1|\le C(R^2/m)\exp(C R^2/m).
\]
Uniformly for integer u >= K_n(h+1), the probability R>=u is at most exp(-c_n u): the last u positions then contain at most h hits, whereas their hypergeometric mean is at least u/n. Apply the sampling-without-replacement lower-tail bound with K_n >= 2n. [Hoeffding, 1963](https://doi.org/10.1080/01621459.1963.10500830).

For R <= K_n(h+1) the displayed error is O_n((h+1)^2/m). Between this cutoff and delta m choose delta so small that the exponential correction costs at most exp(c_n R/2); summing the tail bound times R²/m gives O_n(1/m). Above delta m use the elementary bound D_R(e) <= C(m,h) since it is a probability times that count. Its logarithm is o(m) for h=O(sqrt(m)), so even this coarse bound gives an exponentially negligible tail. These estimates prove the first assertion, including rare labelled patterns.

**Sharp boundary.** With h/sqrt(m) tending to c, R/h tends to n in probability. In the last floor((n+epsilon)h) or floor((n-epsilon)h) positions the expected hit counts bracket h by order h, with variance O(h), since (m+h)/T tends to 1/n. The order statistic characterization gives the claim. To pass conditional estimates to expectations, fix a large K: on R <= K h the bound exp(C R²/m) is bounded, and on larger R the preceding exponential tail argument applies, with the tail tending to zero.

For R=O(h) the denominator tends uniformly to one for n>=3. The chance any one colour is drawn n times is bounded, after a union over times and colours, by binom(R,n) m n! / m-rising-n, of order R^n/m^(n-1). Here m-rising-n denotes m(m+1)...(m+n-1). This tends to zero. For the packed vector, h/N initially saturated colours have total urn weight w=n h/N. With d=R-h new draws, avoiding these colours has probability
\[
 \prod_{j=0}^{d-1}(1-w/(m+h+j)).
\]
When R/h tends to n its log tends to -n c², since d/h tends to N. Conditional on avoidance, the remaining colours form an urn initially of weight one each. The same n-fold repetition bound makes their overflow probability o(1). For the all-distinct initial vector, unoccupied colours again overflow with probability at most O(R^n/m^(n-1)). Each of h occupied colours starts with weight two and needs n-1 new draws to overflow, giving an additional union bound O_n(h R^(n-1)/m^(n-1))=o(1). The distinct profile density thus tends to one. At n=2 each admissible vector has h ones, and its probability is exactly 1/binom(m,h).

**All profiles at the boundary.** More generally let b(e) count the entries equal to N. For n>=3 and h/sqrt(m) tending to c in (0,infinity), uniformly in admissible e,
\[
 C(m,h) Q(E=e)=\exp[-n(n-1)b(e)h/m]\,(1+o(1)).
\]
Indeed the initially saturated sites have total weight n b(e). Avoidance for d draws has the same product as above with w=n b(e). Conditional on avoidance the remaining urn starts with total weight at least m-O(h). Initially occupied unsaturated sites number at most h, have bounded weight and need at least two more hits to overflow. Their combined overflow probability is O_n(h d²/m²), by a union bound over sites and pairs of draws. Empty sites cost O_n(d^n/m^(n-1)) as before. Both errors tend uniformly to zero for R=O(h). The log avoidance probability is -n b(e)d/m+o(1) uniformly there since b(e)<=h and h=O(sqrt(m)). Replacing d by (n-1)h costs o(1) in probability uniformly in e. Use the same bounded central contribution and tail estimates to average. The limiting comparison factors stay uniformly bounded away from zero, so an additive o(1) is also a relative o(1).

**Application to heterogeneous panels.** For positive failure-odds multipliers t_i relative to an interior homogeneous reference, the weighted likelihood on the stratum equals the product of t_i^(n-1) times the expectation under Q of the product of t_i^(-E_i). Below the boundary, approximate that latter expectation by summing the monomials over all capped compositions of h and dividing by C(m,h). At the square-root scale multiply each monomial by the boundary factor above. The same relative accuracy applies by positivity, uniformly in all m multipliers, even when their ratios diverge. Divide the resulting weighted likelihood by the exact full-stratum likelihood to obtain E_het[Z | S=m+h]. The full likelihood is the coefficient of x^(m(n-1)-h) in the product of (1+t_i x)^n divided by binom(mn,m+h).

For fixed h change just one multiplier to 1/(lambda m), lambda>0. The residual factor beyond t_1^(n-1) tends to the sum of (h)_j lambda^j for 0 <= j <= min(h,N), with falling factorial (h)_j. For E_1=j, the number of admissible completions on other tasks is asymptotic to m^(h-j)/(h-j)!: at fixed h-j the leading degree comes from distinct occupied sites. The uniform relative estimate permits summation even with the growing tilt. When h=2 and n>=3, the factor is 1+2 lambda+2 lambda². Assigning the two extras independently to uniformly chosen tasks gives (1+lambda)^2 instead. With lambda=1 the two limiting corrections are five and four. This is a testable discrepancy in the synthetic model, conditional on the observed total.

The earlier [two-extra-hit sign bound](two-extra-successes.md) and [single-extra-hit identity](sparse-threshold-stratum.md) concern the same score. This proof gives relative probabilities and their sharp range of uniformity. Scientific priority outside the programme and empirical applicability to dependent retries remain unverified. This supplement postdates the assessed manuscript.

**Arithmetic checks.** The [certificate](threshold-allocation.py) extracts suffix-vector coefficients for each remaining slot count R and rounds each summand outwards before adding. It cross-checks both labelled types at three tasks and cap three against all 512 full strings and checks the cap-two identity. With n=3, m=1024, h=32, the normalized labelled densities lie in (1.17028,1.17030) for distinct extras and (0.09972,0.09974) for packed pairs. At h=2 for the same bank they lie in (1.00003,1.00004) and (0.98307,0.98308). These finite values are not estimates of an empirical system. [All nineteen certified intervals](threshold-allocation-results.json).
