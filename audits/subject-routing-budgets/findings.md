# Results on the pinned paired responses

The 57 official MMLU subject files contained 14,042 rows. Five rows matched the authors' exclusion list. The analysis retains 14,037 rows with 13,932 distinct prompts. Counts weight each retained row once, including repetitions. The weak model answered 9,558 correctly, the strong model 11,312. There were 2,496 strong-only successes and 742 weak-only successes.

| Condition | Exact number of calls to GPT-4 (inclusive) |
| --- | --- |
| Some overall optimum matches or exceeds the better fixed model in every subject | 1,840 through 13,951 |
| Every overall optimum matches or exceeds that subject-specific floor in every subject | 2,495 through 13,300 |

At 1,306 feasible integer budgets, the choice among tied optima can change whether a subject misses its floor. With exactly 1,840 strong calls two concrete assignments both score 11,398 overall. One meets all 57 floors and scores 724 on moral scenarios. The other scores 385 on that subject, 339 below its floor. This is the largest possible individual subject shortfall over feasible budgets and pooled optimal assignments, measured in numbers of correct answers. Subject sizes differ. A shortfall in counts is not a normalized comparison of sensitivity across subjects.

This result gives evaluators a concrete reason to report subject scores alongside overall accuracy and strong-call counts. The example uses labels in hindsight. It does not show that any learned router chose either allocation. No monetary saving, causal effect, or model capability outside the recorded responses was measured.

The Colab return has SHA-256 `e69329388fb6807b3ca3853ef370e4e6193ad71788dc4ebf0b3b4ac5af72310e`. The JSON supplement inside includes all four directly checked assignments, derived per-subject scores, and all 59 source hashes. The separate GSM8K note uses the same model pair and fixed repository commit.
