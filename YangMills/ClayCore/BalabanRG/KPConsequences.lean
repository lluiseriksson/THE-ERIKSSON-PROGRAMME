import Mathlib
import YangMills.ClayCore.BalabanRG.KPBudgetBridge

namespace YangMills.ClayCore

open scoped BigOperators
open Classical

/-!
# KPConsequences — Layer 4A

Direct consequences of `kpOnGamma_implies_compatibleFamilyMajorant`.

Chain:
  KPOnGamma
    → CompatibleFamilyMajorant (KPBudgetBridge)
    → SmallActivityBudget      (Layer 2)
    → |Z - 1| ≤ exp(budget) - 1
    → 0 < Z
    → log Z ≤ exp(budget) - 1
-/

noncomputable section

/-! ## 4A-1: KP → SmallActivityBudget -/

theorem kpOnGamma_implies_smallActivityBudget {d : ℕ} {L : ℤ}
    (Gamma : Finset (Polymer d L)) (K : Activity d L) (a : ℝ) (ha : 0 < a)
    (hKP : KPOnGamma Gamma K a) :
    SmallActivityBudget Gamma K (Real.exp (theoreticalBudget Gamma K a) - 1) :=
  compatibleFamilyMajorant_implies_smallActivityBudget Gamma K _
    (kpOnGamma_implies_compatibleFamilyMajorant Gamma K a ha hKP)

/-! ## 4A-2: KP → |Z - 1| ≤ exp(budget) - 1 -/

theorem kpOnGamma_implies_abs_Z_sub_one_le {d : ℕ} {L : ℤ}
    (Gamma : Finset (Polymer d L)) (K : Activity d L) (a : ℝ) (ha : 0 < a)
    (hKP : KPOnGamma Gamma K a) :
    |polymerPartitionFunction Gamma K - 1|
      ≤ Real.exp (theoreticalBudget Gamma K a) - 1 :=
  abs_Z_sub_one_le_of_majorant Gamma K _
    (kpOnGamma_implies_compatibleFamilyMajorant Gamma K a ha hKP)

/-! ## 4A-3: KP → 0 < Z  (when budget < 1) -/

theorem polymerPartitionFunction_pos_of_kp {d : ℕ} {L : ℤ}
    (Gamma : Finset (Polymer d L)) (K : Activity d L) (a : ℝ) (ha : 0 < a)
    (hKP : KPOnGamma Gamma K a)
    (hsmall : Real.exp (theoreticalBudget Gamma K a) - 1 < 1) :
    0 < polymerPartitionFunction Gamma K := by
  have habs := kpOnGamma_implies_abs_Z_sub_one_le Gamma K a ha hKP
  have hlt : |polymerPartitionFunction Gamma K - 1| < 1 := lt_of_le_of_lt habs hsmall
  have := abs_sub_lt_iff.mp hlt
  linarith [this.1]

/-! ## 4A-4: KP → log Z ≤ exp(budget) - 1  (when 0 < Z) -/

/-- For x > 0, log x ≤ x - 1.  Specialised here to x = Z. -/
theorem log_le_sub_one_of_pos (x : ℝ) (hx : 0 < x) : Real.log x ≤ x - 1 := by
  have := Real.add_one_le_exp (Real.log x)
  rw [Real.exp_log hx] at this
  linarith

theorem log_polymerPartitionFunction_le_budget {d : ℕ} {L : ℤ}
    (Gamma : Finset (Polymer d L)) (K : Activity d L) (a : ℝ) (ha : 0 < a)
    (hKP : KPOnGamma Gamma K a)
    (hsmall : Real.exp (theoreticalBudget Gamma K a) - 1 < 1) :
    Real.log (polymerPartitionFunction Gamma K)
      ≤ Real.exp (theoreticalBudget Gamma K a) - 1 := by
  have hpos := polymerPartitionFunction_pos_of_kp Gamma K a ha hKP hsmall
  have habs := kpOnGamma_implies_abs_Z_sub_one_le Gamma K a ha hKP
  -- log Z ≤ Z - 1 ≤ |Z - 1| ≤ exp(budget) - 1
  calc Real.log (polymerPartitionFunction Gamma K)
      ≤ polymerPartitionFunction Gamma K - 1 := log_le_sub_one_of_pos _ hpos
    _ ≤ |polymerPartitionFunction Gamma K - 1| := le_abs_self _
    _ ≤ Real.exp (theoreticalBudget Gamma K a) - 1 := habs

end

end YangMills.ClayCore
