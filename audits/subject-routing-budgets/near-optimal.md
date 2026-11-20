# How many correct answers separate a subject failure from the overall optimum?

The published RouteLLM response bank supplies one pair of binary labels for each retained question. Its 57 MMLU subjects partition the rows. Fix exactly k uses of the strong model. Write F(k) for the maximum pooled correct count and B(k) for the largest pooled count among assignments failing at least one subject floor. The floor is the larger of the two fixed-model correct counts on the subject. The margin is F(k)−B(k), or infinity if no assignment can fail. At an integer tolerance e, **all** assignments at most e correct answers below the optimum are safe exactly when the margin exceeds e. Equality is already enough to permit a failure.

## Computing the constrained optimum

Within a subject write n for its size and u,h,z for its positive, negative and zero gains from switching model. Define d = max(0,u−h). Failure requires a subject gain at most d−1. With exactly j subject calls the minimum and maximum possible gains are

    low(j)  = max(0,j−(n−u)) − min(j,h)
    high(j) = min(j,u) − max(0,j−(n−h)).

They are attained by sorting the gains in ascending or descending order. When z=0, the possible gains form the parity class of j between these endpoints. Selecting b negative gains gives j−2b, and all feasible b form an integer interval.

When z>0 every integer between the endpoints occurs. Follow exchanges from a minimum selection to a maximum selection, swapping a smaller selected value for a larger unselected value. A jump of two swaps a negative gain for a positive gain. If a neutral row is unselected, first replace the negative row with that neutral row, then replace the neutral row with the positive row. If the neutral row is selected, first exchange it for the positive row, then exchange the negative row for the neutral row. Both paths visit the intermediate gain. The argument covers j=0 and j=n where the endpoints coincide.

For each feasible j, take the greatest attainable subject gain y(j) at most d−1. Start with min(high(j), d−1), drop one if parity requires it, and discard j if the result falls below low(j). On the complementary rows take the k−j greatest gains. Add the baseline weak score on the whole bank. Maximizing this sum over j and the choice of failing subject gives B(k). Every violation appears in one such term and each term is attained by an allocation. The same allocation can violate multiple floors, which has no effect on a maximum.

The software compares all schedules on 729 six-row paired-gain panels with the resulting margins, including parity gaps and impossible failures. On the benchmark it records extremizing row-index sets at both ends of every constant-margin interval. Empirical conclusions apply to the released rows and count answers, irrespective of unequal token costs.

## Relation to earlier work

Marx, Calmon and Ustun study conflicting predictions among near-optimal classifiers. The present calculation concerns the largest total score compatible with a specified subject failing a baseline on paired, fixed routing outcomes. Recent batch-routing research considers operational cost and capacity constraints; their robust objective addresses uncertain performance estimates. No priority claim is made for near-optimal model comparisons or for separable optimization. [Predictive Multiplicity in Classification](https://proceedings.mlr.press/v119/marx20a.html) · [Robust Batch-Level Query Routing](https://arxiv.org/abs/2603.26796) · [RouteLLM](https://arxiv.org/abs/2406.18665)
