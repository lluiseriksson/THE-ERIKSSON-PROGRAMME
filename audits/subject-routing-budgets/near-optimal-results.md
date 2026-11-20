# Two correct answers exhaust the subject-floor guarantee on this MMLU bank

Across all 14,038 integer strong-call budgets, the smallest pooled loss from the optimum that permits any subject to fall below its better fixed-model count is as follows. Counts refer to the official 14,037 retained rows for the RouteLLM model pair.

| Exactly this many strong calls | Smallest pooled loss permitting a breach |
| --- | ---: |
| 0–2,494 | 0 |
| 2,495 | 1 |
| 2,496–13,299 | 2 |
| 13,300 | 1 |
| 13,301–14,037 | 0 |

At 2,496 calls the maximum is 12,054 correct. An explicit assignment scores 12,052, including 93 in medical genetics against its 94-answer floor. At the same call count **every** assignment scoring at least 12,053 meets all 57 floors. Allowing a loss of two answers from the optimum eliminates the universal guarantee at every budget. This is a statement about the existence of violating allocations. The frequencies under a deployed router are unknown.

The full result file contains the selected row indices for eight witnesses at the endpoints of the five intervals, recomputed subject and pooled counts, and pinned input hashes. The procedure also compared every budget in each of 729 small panels with direct subset enumeration. All these calculations ran on Colab Linux. The returned archive has SHA-256 `70649cbbbe9e7d71e2f0cfa58a1c5fd73776107ba9f2bc7d08e22ebc6564db1f`.

In the same directory, run `python near_optimal.py margin.zip` with Python 3 and NumPy and compare the decompressed JSON. The loader verifies the official RouteLLM Git blobs. No new model generations are needed. This supplement postdates the frozen PDF and its assessment.
