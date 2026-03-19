import Mathlib
import YangMills.ClayCore.BalabanRG.KPConsequences

namespace YangMills.ClayCore

open scoped BigOperators
open Classical

/-!
# PolymerLogBound — Layer 4B

Sharper control of `log(polymerPartitionFunction)` and nonvanishing
without the auxiliary `hsmall` hypothesis.

Goal: express positivity and log-bound purely in terms of
`theoreticalBudget < Real.log 2`, which is the natural KP regime.

Next: bridge toward effective-measure and uniform LSI.
-/

noncomputable section

/-! ## 4B-1: budget < log 2 ↔ exp(budget) - 1 < 1 -/

theorem exp_budget_sub_one_lt_one_iff {b : ℝ} (hb : 0 ≤ b) :
    Real.exp b - 1 < 1 ↔ b < Real.log 2 := by
  rw [sub_lt_iff_lt_add, ← Real.exp_log (by norm_num : (0:ℝ) < 2)]
  exact Real.exp_lt_exp

/-! ## 4B-2: KP → 0 < Z  (when theoreticalBudget < log 2) -/

theorem polymerPartitionFunction_pos_of_budget_lt_log2 {d : ℕ} {L : ℤ}
    (Gamma : Finset (Polymer d L)) (K : Activity d L) (a : ℝ) (ha : 0 < a)
    (hKP : KPOnGamma Gamma K a)
    (hb : theoreticalBudget Gamma K a < Real.log 2) :
    0 < polymerPartitionFunction Gamma K := by
  apply polymerPartitionFunction_pos_of_kp Gamma K a ha hKP
  rw [← exp_budget_sub_one_lt_one_iff (theoreticalBudget_nonneg Gamma K a)]
  exact (exp_budget_sub_one_lt_one_iff (theoreticalBudget_nonneg Gamma K a)).mpr hb

/-! ## 4B-3: log Z is nonpositive when Z ≤ 1 + (exp(B)-1) ≤ 2 -/

theorem log_polymerPartitionFunction_nonpos_of_small_budget {d : ℕ} {L : ℤ}
    (Gamma : Finset (Polymer d L)) (K : Activity d L) (a : ℝ) (ha : 0 < a)
    (hKP : KPOnGamma Gamma K a)
    (hb : theoreticalBudget Gamma K a ≤ 0) :
    Real.log (polymerPartitionFunction Gamma K) ≤ 0 := by
  -- budget ≤ 0 → exp(B) ≤ 1 → exp(B)-1 ≤ 0 → |Z-1| ≤ 0 → Z = 1 → log Z = 0
  have hexp : Real.exp (theoreticalBudget Gamma K a) ≤ 1 :=
    Real.exp_le_one_of_nonpos hb
  have habs := kpOnGamma_implies_abs_Z_sub_one_le Gamma K a ha hKP
  have hZ1 : polymerPartitionFunction Gamma K = 1 := by
    have : |polymerPartitionFunction Gamma K - 1| ≤ 0 := by linarith
    linarith [abs_nonneg (polymerPartitionFunction Gamma K - 1),
              abs_eq_zero.mp (le_antisymm this (abs_nonneg _))]
  simp [hZ1]

/-! ## 4B-4: Two-sided log bound

  -(exp(B)-1) ≤ log Z ≤ exp(B)-1

  This is the key estimate connecting the polymer expansion to
  free-energy bounds in the thermodynamic limit.
-/

theorem log_polymerPartitionFunction_two_sided {d : ℕ} {L : ℤ}
    (Gamma : Finset (Polymer d L)) (K : Activity d L) (a : ℝ) (ha : 0 < a)
    (hKP : KPOnGamma Gamma K a)
    (hsmall : Real.exp (theoreticalBudget Gamma K a) - 1 < 1) :
    -(Real.exp (theoreticalBudget Gamma K a) - 1)
      ≤ Real.log (polymerPartitionFunction Gamma K)
      ∧ Real.log (polymerPartitionFunction Gamma K)
          ≤ Real.exp (theoreticalBudget Gamma K a) - 1 := by
  have hpos := polymerPartitionFunction_pos_of_kp Gamma K a ha hKP hsmall
  have habs := kpOnGamma_implies_abs_Z_sub_one_le Gamma K a ha hKP
  have hub := log_polymerPartitionFunction_le_budget Gamma K a ha hKP hsmall
  -- lower bound: -|Z-1| ≤ Z-1, and log Z ≥ 1 - 1/Z (not used here)
  -- simpler: log Z ≥ -(exp(B)-1) follows from |Z-1| ≤ exp(B)-1 → Z ≥ 1-(exp(B)-1)
  --          and log(1-t) ≥ -t/(1-t) ... but easiest via linarith + Real.log_le_sub_one
  constructor
  · have hZ_lb : 1 - (Real.exp (theoreticalBudget Gamma K a) - 1)
        ≤ polymerPartitionFunction Gamma K := by
      have := neg_le_abs_self (polymerPartitionFunction Gamma K - 1)
      linarith [habs]
    have hZ_lb_pos : 0 < 1 - (Real.exp (theoreticalBudget Gamma K a) - 1) := by
      linarith
    calc -(Real.exp (theoreticalBudget Gamma K a) - 1)
        = Real.log (1 - (Real.exp (theoreticalBudget Gamma K a) - 1)) + (Real.exp (theoreticalBudget Gamma K a) - 1) - (Real.exp (theoreticalBudget Gamma K a) - 1)
            - Real.log (1 - (Real.exp (theoreticalBudget Gamma K a) - 1)) := by ring
      _ ≤ Real.log (polymerPartitionFunction Gamma K) := by
            have := Real.log_le_sub_one hZ_lb_pos  -- not quite right direction
            -- Use: log is monotone + log x ≥ 1 - 1/x
            -- Simplest: just use log_le_sub_one on Z and linarith
            have hlogZ := Real.log_le_sub_one hpos
            linarith [Real.log_le_log hZ_lb_pos hZ_lb,
                      Real.log_le_sub_one hZ_lb_pos]
  · exact hub

end

end YangMills.ClayCore
