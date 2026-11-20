# Sparse heterogeneity at the pooled success threshold

In the [growing-group experiment](growing-exceptions.md), fix the cap n and take k=m+h, with h=o(m), r=o(m). For failure-odds multipliers t_i in any compact subset of (0,infinity),
\[
 \log E[Z\mid S=m+h]=
 \sum_{i=1}^r\log\frac{t_i^{n-1}}{(1/n+(1-1/n)t_i)^n}
 + O\big((r^2+rh)/m\big).
\]
At h=0 the log error is O_n(r^2/m) uniformly for all finite positive multipliers, including arbitrarily large or small ones. The [previous band theorem](near-threshold-strata.md) already proves the finite sign in this region for arbitrary probabilities. The result here quantifies the loss.

For the full uniform stratum, inspect the nr named slots in order. Each conditional probability of a prescribed bit differs from its independent Bernoulli k/(mn) probability by O_n(r/m), since at most nr hits or misses have been removed from a population of order m. Both single-bit probabilities stay bounded away from zero. Every prescribed pattern therefore has log probability within O_n(r^2/m) of its independent value. Replacing k/(mn) by 1/n adds O_n(rh/m) to the log error. These pointwise ratios also bound the ratio after weighting by any nonnegative product of site likelihoods. The independent expectation is the product of (1/n+(1-1/n)t_i)^n.

Under the score-weighted stratum each task has at least one hit. Write d_i for its excess above one: each is at most n-1 and their sum is h. After removing the deterministic factor given by the product of t_i^(n-1), the likelihood is the product of t_i^(-d_i) over named tasks. If h=0 this is one for every multiplier. Otherwise, conditional on the unordered count profile, at most h sites have positive excess. Exchangeability assigns them uniformly to labels. Let J count the named sites with positive excess, and put L=(n-1) max_i |log t_i|. The residual likelihood lies between exp(-LJ) and exp(LJ). Its conditional lower expectation is at least exp(-Lrh/m) by Jensen. For the upper expectation, expand the product of 1+(exp(L)-1) times the indicator of each named site's membership in the occupied set. The probability of any j specified memberships is at most (h/m)^j by sampling without replacement. Thus the upper expectation is at most (1+(exp(L)-1)h/m)^r. Both bounds are independent of the profile. Taking logs and subtracting the full-law result proves the formula.

For n=3 and the paired failure-odds multipliers 1/2 and 2, the threshold factors are 27/32 and 108/125, giving 729/1000 per pair. At any h=o(m) and diverging even r=o(m), the conditional expectation raised to the power 2/r tends to 729/1000. The interior example at k=3m/2 instead gives 5624/6561. These are two conditional comparisons for the same synthetic panel. Unbounded tilts when h>0 may amplify exceptional suffix hits and are outside the uniform bound proved here.
## Why uniformity in the odds changes after one extra hit

At h=1 exactly one task carries the unique extra hit. Under the weighted law its label is uniform. The residual expectation is therefore exactly
\[
 1+\frac{1}{m}\sum_{i=1}^r(t_i^{-1}-1).
\]
The full-law pattern estimate was uniform in the odds. Consequently adding the logarithm of this displayed factor gives a uniform O_n(r^2/m) formula at h=1 for all positive multipliers. Without this correction, even one replacement t=m^{-2} adds log(m+1-1/m) to the purported leading term, while the full-law error is O_n(1/m). This refutes the extension of the uncorrected threshold formula to arbitrarily small odds at h=1.

The [six reproduced intervals](threshold-strata-results.json) use [outward-rounded rational weights](threshold-strata.py), with exhaustive enumeration at four tasks. The numerical checks concern paired odds at surplus zero or one. The extreme-odds counterexample follows from the exact exchangeability identity above.
