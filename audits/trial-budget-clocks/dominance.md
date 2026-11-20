# Pricing an unscored trial

Consider two completed, finite, ordered logs. Give every scored trial unit cost and every unscored trial a common price p between zero and one. Before a first score the reported best is a common bottom symbol; after the last trial keep the last best. These conventions compare the observed records for every nonnegative real budget, without imputing any score to a failed trial. Larger scores are better (negate a loss before applying the result).

For every new record score q of log B, let S_X(q) and F_X(q) count scored and unscored trials through the first time log X reaches or exceeds q. If A never reaches a B record, A cannot dominate B for all budgets at any price. Otherwise the set of prices at which A weakly dominates B at **every** budget is exactly the intersection of [0,1] with the half-lines

    S_A(q) - S_B(q) + p [F_A(q) - F_B(q)] ≤ 0.

Indeed B reaches q at budget S_B(q)+pF_B(q). Dominance requires A to reach q by that budget. Conversely, B's best at any budget after a scored observation is one of these record levels; the corresponding inequality puts a score at least as high into A's affordable prefix. The same argument covers p=0 because deleting the costs of unscored trials introduces no additional scores. If B has no scores, the intersection is unrestricted. In particular the admissible prices form a closed interval or the empty set. The binding target at each endpoint gives a checkable certificate. Dominance at *all budgets* for both endpoint prices implies dominance throughout.

At a **single** budget the endpoint test can miss a reversal. Write x for an unscored trial. Let A=(1,x,x,x,3,0) and B=(0,x,x,2,0). At budget 3, A leads at prices 0 and 1. For 1/3 < p ≤ 1/2, B can afford its score 2 and A has only its score 1. The endpoints differ in inclusion because equality makes a score affordable. Equal-price straight-line interpolation of two reported rankings cannot detect this reversal.

Fixed-target hitting times and fixed-budget incumbents are established evaluations (Hansen, Auger, Brockhoff and Tušar, [COCO performance assessment](https://arxiv.org/abs/1605.03560)). Here the specific accounting choice varies the cost of recorded unscored trials within each realized path. This deterministic certificate does not estimate the wall time of a failure, the performance of a rerun, or a causal effect of training procedure.
