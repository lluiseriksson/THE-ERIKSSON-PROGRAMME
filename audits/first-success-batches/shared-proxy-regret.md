# What a shared proxy cannot decide

Consider the two task-block orders in the [cross-model replay](transfer-order.json). The threshold is 118 hits. We ask if seeing only the external task scores is sufficient to choose the better direction for each possible target. Target identity, target labels and pilot measurements are withheld from the selector. This restriction matters: a selector allowed to use architecture, a historical calibration set or a different order is outside the result.

In the secondary experiment all models assigned to the same nominal family have exactly the same proxy peers. At each task they receive the same sum of public correctness counts and the same task-ID tie breaker. Consequently the two labelled inspection orders are identical across those targets, even though their conditional costs can differ.

| Held-out target in the Llama group | Easier tasks first | Harder tasks first |
|---|---:|---:|
| Llama-3.1-70B-Instruct | 124.68 | 170.53 |
| Llama-3.1-8B-Instruct | 137.65 | 200.41 |
| Meta-Llama-3-8B-Instruct | 219.90 | 183.14 |
| Llama-3.1-Nemotron-70B-Instruct-HF | 170.36 | 198.73 |

A deterministic choice from the shared proxy must pick the same direction in all four cases. It cannot pick the better direction for both Llama-3.1-8B-Instruct and Meta-Llama-3-8B-Instruct. This is stronger than an aggregate count of winning policies: these two targets are observationally indistinguishable under the selector's stated information.

**Sharp two-action regret.** Write $e_i,h_i$ for the two expected costs in the file, and let $A=\max_i(h_i-e_i)_+$ and $B=\max_i(e_i-h_i)_+$. Use the easier-first order with probability $p$ shared across the group, making that choice before inspecting any candidates. The largest excess cost over a target-informed choice of the better of these same two orders is exactly
\[
\max\{(1-p)A,\ pB\}.
\]
For $A,B>0$, the optimum has $p=A/(A+B)$ and worst excess $AB/(A+B)$. Here $A$ is about 62.76 checks and $B$ about 36.76, witnessed by the two 8B targets above. Even the best target-blind mixture therefore incurs about 23.2 additional checks in its worst case. Both orders still recover the exact decision on every panel. The loss concerns information for scheduling, not decision error.

This calculation is conditional on the four released target banks. Its minimax choice uses their historical cost envelope; it supplies a lower bound for every proxy-only mixture on this finite set, not an estimate of an optimal policy on future models. The two-point equalization is elementary decision theory. The contribution is the same-proxy witness in the released cohort. It postdates the pinned inspection-order manuscript.

