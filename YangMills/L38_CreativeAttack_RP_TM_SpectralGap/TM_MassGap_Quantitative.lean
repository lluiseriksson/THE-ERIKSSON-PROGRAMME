/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cowork agent (Claude), under supervision of Lluis Eriksson
-/
import Mathlib
import YangMills.L38_CreativeAttack_RP_TM_SpectralGap.T_SpectralGap_Existence

/-!
# Quantitative mass gap bound (Phase 369)

Quantitative bounds on the mass gap.

## Oracle target

`[propext, Classical.choice, Quot.sound]`.
-/

namespace YangMills.L38_CreativeAttack_RP_TM_SpectralGap

/-! ## §1. Lower bound on mass gap -/

/-- **`m ≥ log(opNorm/(opNorm-δ))` is the explicit formula**. -/
theorem mass_gap_explicit_formula (sgd : SpectralGapData) :
    massGapFromSpectralData sgd =
      Real.log (sgd.opNorm / (sgd.opNorm - sgd.δ)) := rfl

/-- **For default, m = log 2 ≈ 0.693**. -/
theorem default_mass_gap_value :
    massGapFromSpectralData defaultSpectralGapData = Real.log 2 := by
  unfold massGapFromSpectralData lambdaEff defaultSpectralGapData
  simp
  norm_num

#print axioms default_mass_gap_value

/-! ## §2. Mass gap > 1/2 -/

/-- **Default mass gap > 1/2**. -/
theorem default_mass_gap_gt_half :
    (1/2 : ℝ) < massGapFromSpectralData defaultSpectralGapData := by
  rw [default_mass_gap_value]
  -- log 2 > 1/2 ⟺ 2 > exp(1/2).
  have h_exp_half_sq : Real.exp (1/2 : ℝ) ^ 2 = Real.exp 1 := by
    rw [sq, ← Real.exp_add]; norm_num
  have h_e_lt_4 : Real.exp 1 < 4 := by
    have := Real.exp_one_lt_d9; linarith
  have h_exp_half_lt_2 : Real.exp (1/2 : ℝ) < 2 := by
    have h_exp_half_pos : 0 < Real.exp (1/2 : ℝ) := Real.exp_pos _
    nlinarith [h_exp_half_sq, h_e_lt_4, h_exp_half_pos]
  have : (1/2 : ℝ) = Real.log (Real.exp (1/2)) := (Real.log_exp _).symm
  rw [this]
  exact Real.log_lt_log (Real.exp_pos _) h_exp_half_lt_2

#print axioms default_mass_gap_gt_half

/-! ## §3. Robustness -/

/-- **For any spectral gap data with `opNorm/λ_eff ≥ 2`, mass gap ≥ log 2**. -/
theorem mass_gap_robust_lower_bound (sgd : SpectralGapData)
    (h_ratio : 2 ≤ sgd.opNorm / lambdaEff sgd.opNorm sgd.δ) :
    Real.log 2 ≤ massGapFromSpectralData sgd := by
  unfold massGapFromSpectralData
  exact Real.log_le_log (by norm_num : (0:ℝ) < 2) h_ratio

#print axioms mass_gap_robust_lower_bound

end YangMills.L38_CreativeAttack_RP_TM_SpectralGap
