# Does a change in regional dispersion survive changing the index origin?

Mohan and Chattopadhyay report an Economic Progress Index for Maharashtra. Their Table 6 contains the population-weighted mean index for each of six revenue divisions in two four-quarter windows. The authors already explain that relative measures depend on the chosen origin. We ask a narrower question about the published endpoints. Can two relative measures indicate opposite directions of change for the same recoding and the same scores?

**Yes.** For the nonnegative PCA specification, add any common offset c from 0.309 through 0.362 in the original index units. The later coefficient of variation is smaller, but the ratio of the largest division mean to the smallest is larger. For standard PCA a certified interval with the same disagreement is 0.368 through 0.440. These intervals allow every displayed input to differ from its latent value by up to 0.00005. They need not be maximal. Adding c and then dividing all scores by 1+c preserves the upper endpoint 1 and yields the same ratios. Such a recoding changes the reported scale's origin; this is a sensitivity analysis. No alternative origin is proposed as economically preferable.

| Specification | Switching point for max/min | Switching point for CV |
| --- | --- | --- |
| Nonnegative PCA | between 0.304 and 0.309 | between 0.362 and 0.369 |
| Standard PCA | between 0.363 and 0.368 | between 0.440 and 0.447 |

## Why the thresholds differ

For period t, let m be the mean of the six division values, s their sample standard deviation, a their minimum, and r their range. After adding c, the coefficient of variation is s/(m+c), while the maximum-to-minimum ratio is 1+r/(a+c). For either metric the change between periods has the sign of a linear function

    numerator = v1 b0 − v0 b1 + (v1−v0)c,

where (v,b) is (s,m) or (r,a). The table certifies that both s and r increased in each PCA specification. The line's slope is strictly positive, so sign checks at two shifts bracket its unique zero. Different numerators can reverse at different shifts.

The computation uses rational arithmetic. For CV, it compares squared values using s² = sum of squared pairwise differences divided by n(n−1). Independent rounding boxes give upper and lower bounds for each pairwise difference, the positive mean and the extrema. These bounds may be conservative because a single choice of latent scores need not realize all extrema together. They certify the signs throughout the displayed intervals by the single-crossing argument. The result concerns endpoint cross-sections of division-level means with equal weight per division. It does not test the significance of the original quarterly trend.

## Scope and sources

The general dependence on the origin is established measurement theory and is explicitly recognized in the application itself. The numerical separation of the two switching intervals for both specifications is the result of this audit. A rising max/min ratio and a falling CV answer different questions about the endpoints. Neither statistic alone determines the redistribution of all six relative shares. [Original Table 6 and discussion](https://arxiv.org/html/2611.23798v1#S4.T6) · [Kolm, Unequal Inequalities I](https://doi.org/10.1016/0022-0531(76)90037-5)

Run the scripts in an authorized Linux environment with Python 3 and Beautiful Soup. Each reads the primary table and records the response hash. The primary HTML used here has SHA-256 `eea93e79dc53f8cfae4df9eecbbe0534ce314ac59573b22a24b60f234defa489`. The archived output contains derived bounds.
