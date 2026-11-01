# One next question and reproducible formalization plan

Question: can the actual finite numerical rank and full-integer-side family density consequences be derived in Lean from actualVolumeMean_nonlinear_rank without a supplied spectral or kernel certificate?

Retained hypotheses: positive-total occupied means with common m>=0, actual flat packet, original local nonlinear hypotheses separately at each n; c>0 common for density. No original-weight lower bound or uniform K/delta/radius is added.

First formal target: use centeredFourier_multiplier_sum_sq_le at coexactPositiveFourierIndex to derive the sum bound, count BOTH real quadratures, and prove the finite H*(1-m*B/c) rank bound. Then use floor(alpha*n), derived cutoff/cardinality and limits for a full-tail density. Sharper exact finite sum and sinc/optimized constants in proof.md are analytic until separately compiled.

Mechanism: existing checked finite endpoint -> actual numerical multiplier sum -> finite rank rearrangement -> positive family density. No certificate structure replacing a missing inequality. Falsifiers: frequency wrap/omitted derivative direction, missing quadrature, wrong floor count, signed mean substitution, c0 division or hidden uniformity.

Abandon/change route after three substantive units without a proved endpoint or useful counterexample; retain failures and exact blocker. Check PR136 final-head required checks before normal integration. Consolidate related substantial results in existing manuscript, reconcile pending v5 first, then visually verify/score its exact PDF. No separate small-corollary paper.
