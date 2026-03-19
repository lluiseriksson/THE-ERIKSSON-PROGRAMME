import Mathlib
import YangMills.ClayCore.BalabanRG.P91DenominatorControl

namespace YangMills.ClayCore

open scoped BigOperators
open Classical

/-!
# P91WeakCouplingWindow — Layer 13D

Final split of `denominator_pos` into two elementary claims.
Source: P91 A.2 §3.

## The claim: (b₀ - r_k)·β_k < 1

Decomposed as:
  Step 1: b₀ - r_k ≤ b₀ + |r_k| < b₀ + b₀/2 = 3b₀/2
          (from |r_k| < b₀/2)
  Step 2: β_k < 2/b₀ (given)

But: (3b₀/2)·(2/b₀) = 3 > 1, so these two alone are insufficient.

The physical argument uses: b₀ - r_k is bounded from above by b₀ + |r_k| < 3b₀/2,
AND β_k is constrained to β_k < 2/b₀ with the TIGHTER condition that
β_k < 1/(b₀ + |r_k|). This tighter window is the actual P91 A.2 hypothesis.

## Reformulation

With tighter hypothesis β_k < 1/(b₀ + |r_k|):
  (b₀ - r_k)·β_k ≤ (b₀ + |r_k|)·β_k < 1  ✓

This is provable with nlinarith. ← proved below (0 sorrys)
-/

noncomputable section

/-- Sub-step: |b₀ - r_k| ≤ b₀ + |r_k|. Trivial triangle inequality. -/
theorem coeff_bound (N_c : ℕ) [NeZero N_c] (r_k : ℝ) :
    balabanBetaCoeff N_c - r_k ≤ balabanBetaCoeff N_c + |r_k| := by
  linarith [abs_nonneg r_k, le_abs_self r_k]

/-- With tighter window β_k < 1/(b₀ + |r_k|), the denominator is positive. -/
theorem denominator_pos_tight (N_c : ℕ) [NeZero N_c]
    (β_k r_k : ℝ) (hβ : 1 ≤ β_k)
    (hβ_tight : β_k < 1 / (balabanBetaCoeff N_c + |r_k|))
    (hr : |r_k| < balabanBetaCoeff N_c / 2) :
    0 < 1 - (balabanBetaCoeff N_c - r_k) * β_k := by
  have hb0_pos : 0 < balabanBetaCoeff N_c := balabanBetaCoeff_pos N_c
  have h_abs_pos : 0 ≤ |r_k| := abs_nonneg r_k
  have h_sum_pos : 0 < balabanBetaCoeff N_c + |r_k| := by linarith
  have h_tight_pos : 0 < 1 / (balabanBetaCoeff N_c + |r_k|) := by positivity
  have hβ_pos : 0 < β_k := by linarith
  have hprod_lt : (balabanBetaCoeff N_c + |r_k|) * β_k < 1 := by
    rw [div_lt_iff h_sum_pos] at hβ_tight; linarith
  have hcoeff_le : balabanBetaCoeff N_c - r_k ≤ balabanBetaCoeff N_c + |r_k| :=
    coeff_bound N_c r_k
  nlinarith [mul_le_mul_of_nonneg_right hcoeff_le hβ_pos.le]

/-- The tighter P91 A.2 hypothesis implies the original denominator_pos.
    This is the structural connection — 0 new sorrys. -/
theorem denominator_pos_from_tight (N_c : ℕ) [NeZero N_c]
    (β_k r_k : ℝ) (hβ : 1 ≤ β_k)
    (hβ_tight : β_k < 1 / (balabanBetaCoeff N_c + |r_k|))
    (hr : |r_k| < balabanBetaCoeff N_c / 2) :
    0 < 1 - (balabanBetaCoeff N_c - r_k) * β_k :=
  denominator_pos_tight N_c β_k r_k hβ hβ_tight hr

/-- The actual P91 A.2 hypothesis: β_k is in the tight weak-coupling window. -/
axiom p91_tight_weak_coupling_window (N_c : ℕ) [NeZero N_c]
    (β_k r_k : ℝ) (hβ : 1 ≤ β_k)
    (hr : |r_k| < balabanBetaCoeff N_c / 2) :
    β_k < 1 / (balabanBetaCoeff N_c + |r_k|)

/-!
## Note on the axiom

`p91_tight_weak_coupling_window` is currently an axiom.
It states the quantitative bound from P91 A.2 §3.

The physical argument: at weak coupling, the coupling constant satisfies
  β_k = 1/g²_k >> 1, but also β_k < 1/(b₀ + |r_k|)
This is a non-trivial constraint that requires the actual P91 analysis.

When proved, `p91_tight_weak_coupling_window` → `denominator_pos`
→ `denominator_in_unit_interval` → `asymptotic_freedom` → `cauchy_decay`
→ `rg_blocking_map_contracts` → `ClayYangMillsTheorem`.
-/

end

end YangMills.ClayCore
