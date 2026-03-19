import Mathlib
import YangMills.ClayCore.BalabanRG.KPConsequences

namespace YangMills.ClayCore

open scoped BigOperators
open Classical

/-!
# PolymerLogBound — Layer 4B (minimal, clean)

Finite-log consequences of the KP bounds.

* `exp(theoreticalBudget)-1 < 1` ↔ `theoreticalBudget < log 2`
* positivity / nonvanishing of Z
* upper log bound under the natural `theoreticalBudget < log 2` regime

Lower/two-sided log bound postponed to Layer 4C.
-/

noncomputable section

/-! ## 4B-1: exp(b) - 1 < 1 ↔ b < log 2 -/

theorem exp_budget_sub_one_lt_one_iff {b : ℝ} (hb : 0 ≤ b) :
    Real.exp b - 1 < 1 ↔ b < Real.log 2 := by
  have h2 : (0 : ℝ) < 2 := by norm_num
  constructor
  · intro h
    rw [sub_lt_iff_lt_add] at h
    norm_num at h
    have h' : Real.exp b < Real.exp (Real.log 2) := by
      simpa [Real.exp_log h2] using h
    exact Real.exp_lt_exp.mp h'
  · intro h
    rw [sub_lt_iff_lt_add]
    norm_num
    have h' : Real.exp b < Real.exp (Real.log 2) := Real.exp_lt_exp.mpr h
    simpa [Real.exp_log h2] using h'


/-! ## 4B-2: KP → 0 < Z when theoreticalBudget < log 2 -/

theorem polymerPartitionFunction_pos_of_budget_lt_log2 {d : ℕ} {L : ℤ}
    (Gamma : Finset (Polymer d L)) (K : Activity d L) (a : ℝ) (ha : 0 < a)
    (hKP : KPOnGamma Gamma K a)
    (hb : theoreticalBudget Gamma K a < Real.log 2) :
    0 < polymerPartitionFunction Gamma K := by
  have hsmall : Real.exp (theoreticalBudget Gamma K a) - 1 < 1 :=
    (exp_budget_sub_one_lt_one_iff (theoreticalBudget_nonneg Gamma K a)).2 hb
  exact polymerPartitionFunction_pos_of_kp Gamma K a ha hKP hsmall

theorem polymerPartitionFunction_ne_zero_of_budget_lt_log2 {d : ℕ} {L : ℤ}
    (Gamma : Finset (Polymer d L)) (K : Activity d L) (a : ℝ) (ha : 0 < a)
    (hKP : KPOnGamma Gamma K a)
    (hb : theoreticalBudget Gamma K a < Real.log 2) :
    polymerPartitionFunction Gamma K ≠ 0 :=
  ne_of_gt (polymerPartitionFunction_pos_of_budget_lt_log2 Gamma K a ha hKP hb)

/-! ## 4B-3: theoreticalBudget ≤ 0 → Z = 1 → log Z = 0 -/

theorem log_polymerPartitionFunction_nonpos_of_nonpositive_budget {d : ℕ} {L : ℤ}
    (Gamma : Finset (Polymer d L)) (K : Activity d L) (a : ℝ) (ha : 0 < a)
    (hKP : KPOnGamma Gamma K a)
    (hb : theoreticalBudget Gamma K a ≤ 0) :
    Real.log (polymerPartitionFunction Gamma K) ≤ 0 := by
  have htb0 : theoreticalBudget Gamma K a = 0 :=
    le_antisymm hb (theoreticalBudget_nonneg Gamma K a)
  have habs := kpOnGamma_implies_abs_Z_sub_one_le Gamma K a ha hKP
  have hzero_le : |polymerPartitionFunction Gamma K - 1| ≤ 0 := by
    simpa [htb0] using habs
  have hzero_eq : |polymerPartitionFunction Gamma K - 1| = 0 :=
    le_antisymm hzero_le (abs_nonneg _)
  have hZ1 : polymerPartitionFunction Gamma K = 1 := by
    have : polymerPartitionFunction Gamma K - 1 = 0 := abs_eq_zero.mp hzero_eq
    linarith
  simp [hZ1]

/-! ## 4B-4: upper log bound under theoreticalBudget < log 2 -/

theorem log_polymerPartitionFunction_le_budget_of_budget_lt_log2 {d : ℕ} {L : ℤ}
    (Gamma : Finset (Polymer d L)) (K : Activity d L) (a : ℝ) (ha : 0 < a)
    (hKP : KPOnGamma Gamma K a)
    (hb : theoreticalBudget Gamma K a < Real.log 2) :
    Real.log (polymerPartitionFunction Gamma K)
      ≤ Real.exp (theoreticalBudget Gamma K a) - 1 :=
  log_polymerPartitionFunction_le_budget Gamma K a ha hKP
    ((exp_budget_sub_one_lt_one_iff (theoreticalBudget_nonneg Gamma K a)).2 hb)

end

end YangMills.ClayCore
