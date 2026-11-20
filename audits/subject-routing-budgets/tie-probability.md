# How often a uniform choice among optimal allocations meets all subject floors

The distinction between existence and a guarantee gives no frequency without a model for selecting among ties. As a sensitivity analysis, choose uniformly among the schedules that maximize the pooled count at each exact budget. This describes a hypothetical tie-breaking mechanism on the fixed MMLU response bank. A learned router may follow a different mechanism.

At the first feasible budget L = 1,840, every call selects one of the U = 2,496 strong-only successes. Safety requires at least d_g = max(0,u_g−h_g) selections in each subject g. Their sum is L. Thus exactly d_g selections must fall in each subject. The exact probability of meeting all 57 floors is the product of the binomial coefficients C(u_g,d_g) divided by C(U,L), approximately **5.87815 × 10⁻¹²⁹**. This is the probability that all floors are met, not the probability of the 339-answer example.

At 2,494 calls there are two omitted positive gains. A single omission anywhere is safe. Both omissions can cause a breach only if they come from the same subject with capacity for exactly one omission. Direct enumeration finds **933 of 3,113,760** omission pairs cause a failure (about 0.0300%). At 2,495 calls no pair needs to be omitted and every choice is safe. The exact risk at 2,494 confirms that the lower universal endpoint cannot be reduced by one.

The JSON supplement retains the exact integer fractions and model assumption. The reproduction script compares the product formula to exhaustive subset counts in small populations, then enumerates every two-omission pair on the official panel. This supplement postdates the frozen PDF.
