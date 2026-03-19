import Mathlib
import YangMills.ClayCore.BalabanRG.PolymerLogBound

namespace YangMills.ClayCore

open scoped BigOperators
open Classical

/-!
# PolymerLogLowerBound — Layer 4C

Lower and two-sided bounds on `log(polymerPartitionFunction)`.

Strategy: |Z-1| ≤ t → Z ≥ 1-t → log Z ≥ log(1-t) ≥ -t/(1-t) ≥ -2t (for t ≤ 1/2).
Uses `log_le_sub_one_of_pos` (already proved in KPConsequences) for the aux lemmas.
-/

noncomputable section

/-! ## Auxiliary: log(1-t) ≥ -t/(1-t) for 0 ≤ t < 1 -/

/-- For `0 ≤ t < 1`: `log(1-t) ≥ -t/(1-t)`.
    Proof: apply `log x ≤ x-1` to `x = 1/(1-t)` and rearrange. -/
theorem Real.log_one_sub_ge {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    -(t / (1 - t)) ≤ Real.log (1 - t) := by
  have h1t : 0 < 1 - t := by linarith
  have hpos_inv : 0 < 1 / (1 - t) := one_div_pos.mpr h1t
  -- log(1/(1-t)) ≤ 1/(1-t) - 1
  have hlog : Real.log (1 / (1 - t)) ≤ 1 / (1 - t) - 1 :=
    log_le_sub_one_of_pos (1 / (1 - t)) hpos_inv
  -- log(1/(1-t)) = -log(1-t)
  have hrewrite : Real.log (1 / (1 - t)) = -Real.log (1 - t) := by
    rw [Real.log_div (by norm_num : (1:ℝ) ≠ 0) h1t.ne', Real.log_one, zero_sub]
  rw [hrewrite] at hlog
  -- 1/(1-t) - 1 = t/(1-t)
  have hfrac : 1 / (1 - t) - 1 = t / (1 - t) := by
    field_simp [h1t.ne']; ring
  rw [hfrac] at hlog
  linarith

/-- Weak bound: `log(1-t) ≥ -2t` for `0 ≤ t ≤ 1/2`. -/
theorem Real.log_one_sub_ge_neg_two {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ 1/2) :
    -2 * t ≤ Real.log (1 - t) := by
  have ht1 : t < 1 := by linarith
  have h1t : 0 < 1 - t := by linarith
  have hbase : -(t / (1 - t)) ≤ Real.log (1 - t) := Real.log_one_sub_ge ht0 ht1
  -- t/(1-t) ≤ 2t when t ≤ 1/2
  have hfrac : t / (1 - t) ≤ 2 * t := by
    field_simp [h1t.ne']
    nlinarith
  linarith

/-! ## 4C-1: Z ≥ 1 - (exp(B)-1) -/

theorem polymerPartitionFunction_lb {d : ℕ} {L : ℤ}
    (Gamma : Finset (Polymer d L)) (K : Activity d L) (a : ℝ) (ha : 0 < a)
    (hKP : KPOnGamma Gamma K a) :
    1 - (Real.exp (theoreticalBudget Gamma K a) - 1)
      ≤ polymerPartitionFunction Gamma K := by
  have habs := kpOnGamma_implies_abs_Z_sub_one_le Gamma K a ha hKP
  have hneg : -(Real.exp (theoreticalBudget Gamma K a) - 1)
      ≤ polymerPartitionFunction Gamma K - 1 := by
    linarith [neg_abs_le (polymerPartitionFunction Gamma K - 1)]
  linarith

/-! ## 4C-2: log Z ≥ -t/(1-t) -/

theorem log_polymerPartitionFunction_lower {d : ℕ} {L : ℤ}
    (Gamma : Finset (Polymer d L)) (K : Activity d L) (a : ℝ) (ha : 0 < a)
    (hKP : KPOnGamma Gamma K a)
    (hsmall : Real.exp (theoreticalBudget Gamma K a) - 1 < 1) :
    -((Real.exp (theoreticalBudget Gamma K a) - 1)
        / (1 - (Real.exp (theoreticalBudget Gamma K a) - 1)))
      ≤ Real.log (polymerPartitionFunction Gamma K) := by
  set t := Real.exp (theoreticalBudget Gamma K a) - 1
  have ht0 : 0 ≤ t := by
    change 0 ≤ Real.exp (theoreticalBudget Gamma K a) - 1
    linarith [Real.one_le_exp (theoreticalBudget_nonneg Gamma K a)]
  have ht1 : t < 1 := hsmall
  have hZlb := polymerPartitionFunction_lb Gamma K a ha hKP
  have hZlb_pos : 0 < 1 - t := by linarith
  have hlog_mono : Real.log (1 - t) ≤ Real.log (polymerPartitionFunction Gamma K) :=
    Real.log_le_log hZlb_pos hZlb
  linarith [Real.log_one_sub_ge ht0 ht1]

/-! ## 4C-3: |log Z| ≤ 2t when t ≤ 1/2 (budget < log(3/2)) -/

theorem log_polymerPartitionFunction_abs_le {d : ℕ} {L : ℤ}
    (Gamma : Finset (Polymer d L)) (K : Activity d L) (a : ℝ) (ha : 0 < a)
    (hKP : KPOnGamma Gamma K a)
    (hsmall : Real.exp (theoreticalBudget Gamma K a) - 1 ≤ 1/2) :
    |Real.log (polymerPartitionFunction Gamma K)|
      ≤ 2 * (Real.exp (theoreticalBudget Gamma K a) - 1) := by
  set t := Real.exp (theoreticalBudget Gamma K a) - 1
  have ht0 : 0 ≤ t := by
    change 0 ≤ Real.exp (theoreticalBudget Gamma K a) - 1
    linarith [Real.one_le_exp (theoreticalBudget_nonneg Gamma K a)]
  have ht05 : t ≤ 1/2 := hsmall
  have hsmall1 : t < 1 := by linarith
  have hZlb := polymerPartitionFunction_lb Gamma K a ha hKP
  have hZlb_pos : 0 < 1 - t := by linarith
  have hub := log_polymerPartitionFunction_le_budget Gamma K a ha hKP hsmall1
  have hlb_log : -2 * t ≤ Real.log (1 - t) := Real.log_one_sub_ge_neg_two ht0 ht05
  have hlog_mono : Real.log (1 - t) ≤ Real.log (polymerPartitionFunction Gamma K) :=
    Real.log_le_log hZlb_pos hZlb
  rw [abs_le]
  constructor <;> linarith

end

end YangMills.ClayCore
