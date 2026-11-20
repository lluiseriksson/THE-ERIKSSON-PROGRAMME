# Can the best overall routing score hide subject-level losses?

Consider a benchmark with two recorded binary correctness labels per question and disjoint subjects. Assign exactly k questions to the designated strong model and the rest to the weak model. Each question counts once. An assignment is subject-safe when, in every subject, it achieves at least the larger of the two fixed-model scores there. This is a diagnostic using observed labels after evaluation. A deployed router would have to choose before observing those labels.

## Exact budgets

For subject g let n be its size, w its weak-model score, u the number correct only for the strong model, and h the number correct only for the weak model. Its fixed-model floor is t = max(w,w+u−h). Strong assignments carry marginal gains +1, 0, or −1 relative to the weak baseline. Sorting in descending order gives the best possible score with j calls as

    w + min(j,u) − max(0,j−(n−h)).

An exchange argument proves optimality. An inverted pair of marginal gains can be swapped without lowering the score. The floor therefore permits exactly the integer interval from L = t−w through R = min(n,n−h+w+u−t). These endpoints are attained. Across disjoint subjects the permissible global budgets are all integers from the sum of L through the sum of R. Starting at the lower endpoints and raising individual counts one at a time constructs every intermediate budget.

**At every feasible budget a safe assignment attains the unconstrained pooled optimum.** Within each subject force its first L marginal gains into the chosen set and forbid its last n−R. Every forced gain is positive, and every forbidden gain is negative. Fill the remaining slots with the largest available gains over the entire corpus. For any feasible budget this selects the same multiset of marginal values as unrestricted sorting. In particular, feasibility imposes no penalty on the optimal total, even when tie-breaking matters to individual subjects.

## What a pooled optimum guarantees

Write N, U, H for corpus-wide totals of n, u, h. Every pooled optimum at budget k uses exactly p = min(k,U) positive and m = max(0,k−(N−H)) negative gains. Within subject g the lowest score among all such optima is exactly

    w_g + max(0,p−(U−u_g)) − min(h_g,m).

To attain the bound select positive gains outside g first and negative gains inside g first, then fill the zero-gain slots. These choices act on disjoint sets. To certify that *every* optimal assignment meets *every* floor, check this expression against each subject's floor. A failure for one subject gives an actual counterexample at the specified budget. Per-subject worst cases need not occur in the same assignment.

## Reproduction and scope

Use Python 3 on an authorized Linux runtime and run `python mmlu.py results.zip`. The script fetches the RouteLLM repository at commit `0b64fdafe049e596a3f5657c219329f24af24198`, verifies each input against its pinned Git blob, and applies the authors' prompt-exclusion rule. Duplicate retained questions keep their original weight. The output contains checksums, grouped counts, exact intervals and row-index assignments. Indices are zero-based in the official domain-list order and the within-file order after filtering. It includes an exhaustive four-question, two-subject check. Call budgets count questions, not tokens or monetary costs. The findings concern the supplied models, recorded answers and filters.

The paired responses were released by the RouteLLM authors. MMLU supplies the subject structure. Comparing the authors' optional ceiling with an exact-count ceiling concerns the interpretation of a reference curve. All empirical conclusions here concern the fixed benchmark. A claim of generalization would require prospective or held-out evaluation. [RouteLLM paper](https://arxiv.org/abs/2406.18665) · [Pinned evaluation code and data](https://github.com/lm-sys/RouteLLM/tree/0b64fdafe049e596a3f5657c219329f24af24198/routellm/evals) · [MMLU paper](https://arxiv.org/abs/2009.03300)
