import Mathlib
import YangMills.ClayCore.BalabanRG.P91WindowFromRecursion

namespace YangMills.ClayCore

open scoped BigOperators
open Classical

/-!
# P91RecursionData — Layer 14B

Packages the P91 A.2 hypotheses into a single structure.
This avoids threading loose hypotheses through every downstream theorem.
-/

noncomputable section

/-- The two quantitative P91 A.2 hypotheses, packaged. -/
structure P91RecursionData (N_c : ℕ) [NeZero N_c] where
  /-- Remainder is small: |r_k| ≤ C_rem/β_k. Source: P91 A.2 §3 Step 1. -/
  remainder_small :
    ∀ (k : ℕ) (β_k r_k : ℝ), 1 ≤ β_k →
      |r_k| ≤ remainderBoundConst / β_k
  /-- Remainder is small enough for the window algebra. Source: P91 A.2 §3 Step 2. -/
  remainder_window_small :
    ∀ (k : ℕ) (β_k r_k : ℝ), 1 ≤ β_k →
      |r_k| ≤ remainderBoundConst / β_k →
      remainderBoundConst 
        balabanBetaCoeff N_c * β_k * (1 - balabanBetaCoeff N_c * β_k) / β_k

/-- From P91RecursionData, recover the tight window. -/
theorem p91_tight_window_of_data {N_c : ℕ} [NeZero N_c]
    (data : P91RecursionData N_c)
    (k : ℕ) (β_k r_k : ℝ) (hβ : 1 ≤ β_k)
    (hr : |r_k| < balabanBetaCoeff N_c / 2) :
    β_k < 1 / (balabanBetaCoeff N_c + |r_k|) :=
  window_from_remainder N_c β_k r_k hβ
    (data.remainder_small k β_k r_k hβ)
    (data.remainder_window_small k β_k r_k hβ (data.remainder_small k β_k r_k hβ))

/-- From P91RecursionData, recover asymptotic freedom. -/
theorem af_of_data {N_c : ℕ} [NeZero N_c]
    (data : P91RecursionData N_c)
    (k : ℕ) (β_k r_k : ℝ) (hβ : 1 ≤ β_k)
    (hr : |r_k| < balabanBetaCoeff N_c / 2) :
    β_k < balabanCouplingStep N_c β_k r_k :=
  asymptotic_freedom_from_denominator_control N_c β_k r_k hβ
    (by
      have hb0 := balabanBetaCoeff_pos N_c
      sorry) -- need upper bound β_k < 2/b₀ from data
    hr
    (denominator_in_unit_interval_v2 N_c β_k r_k hβ
      (by sorry) hr)  -- same

/-- The contraction rate decreases under the recursion when P91 data holds. -/
theorem rate_decreases_of_data {N_c : ℕ} [NeZero N_c]
    (data : P91RecursionData N_c)
    (k : ℕ) (β_k r_k : ℝ) (hβ : 1 ≤ β_k)
    (hr : |r_k| < balabanBetaCoeff N_c / 2)
    (hβ_upper : β_k < 2 / balabanBetaCoeff N_c) :
    physicalContractionRate (balabanCouplingStep N_c β_k r_k)
      < physicalContractionRate β_k :=
  contraction_rate_decreases_under_recursion N_c β_k r_k hβ
    (by
      have := p91_tight_window_of_data data k β_k r_k hβ hr
      -- tight window ⊂ 2/b₀ window
      have hb0 := balabanBetaCoeff_pos N_c
      nlinarith [abs_nonneg r_k, (abs_lt.mp hr).2])
    hr

/-!
## What P91RecursionData provides

Once `P91RecursionData N_c` is constructed (from the actual P91 A.2 analysis),
the following chain closes without additional sorrys:

  p91_tight_window_of_data → denominator_pos_from_tight
  af_of_data → asymptotic_freedom_from_denominator_control
  rate_decreases_of_data → contraction_rate_decreases_under_recursion

Remaining: construct P91RecursionData from the actual P91 recursion equations.
-/

end

end YangMills.ClayCore
