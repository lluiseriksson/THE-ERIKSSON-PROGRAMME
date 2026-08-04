/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.PhysicalPoincareCriticalRescaling

/-!
# Scale-adapted Combes--Thomas parameter audit

For the critically rescaled four-dimensional block term the natural sharp
entrywise scale is `L⁻⁴`, the proved fine-metric range certificate is `3L`,
and the standard physical-bond ball majorant is
`(2(3L+1))⁴ * 4`.  This file proves the scalar compensation

`L⁻⁴ * (2(3L+1))⁴ * 4 ≤ 16384`

and constructs a positive block-scale tilt `tau` for every positive coercivity
constant.  The corresponding fine-lattice tilt is `theta_L = tau / L`, so
`theta_L * (3L) = 3 tau` exactly and the CT budget is uniform after the
kernel/ball product has been bounded by `16384`.

This is a parameter theorem, not the missing operator theorem: the sharp
`L⁻⁴` kernel estimate for the critically rescaled Gram term and the all-mode
coercivity estimate remain separate obligations.
-/

namespace YangMills.RG

/-- The universal four-dimensional kernel-times-ball constant produced by the
elementary estimate `3L+1 ≤ 4L`. -/
def criticalCTConstant : ℝ := 16384

/-- Real-valued form of the standard physical-bond ball majorant at range
`3L` in dimension four. -/
def criticalBallMajorant (L : ℕ) : ℝ :=
  (2 * (3 * (L : ℝ) + 1)) ^ 4 * 4

/-- Candidate sharp kernel amplitude for the critically rescaled Gram term. -/
noncomputable def criticalKernelMajorant (L : ℕ) : ℝ :=
  ((L : ℝ) ^ 4)⁻¹

/-- In four dimensions the candidate `L⁻⁴` kernel amplitude exactly
compensates the `O(L⁴)` ball cardinality, uniformly in `L`. -/
theorem criticalKernel_mul_ball_le (L : ℕ) [NeZero L] :
    criticalKernelMajorant L * criticalBallMajorant L ≤ criticalCTConstant := by
  let x : ℝ := L
  have hx : 0 < x := by
    dsimp [x]
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hx1 : 1 ≤ x := by
    dsimp [x]
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne L)
  have hlin : 2 * (3 * x + 1) ≤ 8 * x := by nlinarith
  have hnonneg : 0 ≤ 2 * (3 * x + 1) := by positivity
  have hpow : (2 * (3 * x + 1)) ^ 4 ≤ (8 * x) ^ 4 :=
    pow_le_pow_left₀ hnonneg hlin 4
  have hx4 : 0 < x ^ 4 := by positivity
  rw [criticalKernelMajorant, criticalBallMajorant, criticalCTConstant]
  change (x ^ 4)⁻¹ * ((2 * (3 * x + 1)) ^ 4 * 4) ≤ 16384
  rw [inv_mul_eq_div, div_le_iff₀ hx4]
  calc
    (2 * (3 * x + 1)) ^ 4 * 4 ≤ (8 * x) ^ 4 * 4 :=
      mul_le_mul_of_nonneg_right hpow (by norm_num)
    _ = 16384 * x ^ 4 := by ring

/-- Block-scale tilt rate associated with coercivity `c`. -/
noncomputable def criticalBlockTiltRate (c : ℝ) : ℝ :=
  Real.log (1 + c / (2 * criticalCTConstant)) / 3

theorem criticalBlockTiltRate_pos {c : ℝ} (hc : 0 < c) :
    0 < criticalBlockTiltRate c := by
  have hC : 0 < criticalCTConstant := by norm_num [criticalCTConstant]
  have hquot : 0 < c / (2 * criticalCTConstant) := by positivity
  have hz : 1 < 1 + c / (2 * criticalCTConstant) := by linarith
  exact div_pos (Real.log_pos hz) (by norm_num)

/-- The chosen block-scale rate saturates the uniform scalar CT budget. -/
theorem criticalBlockTiltRate_budget_eq {c : ℝ} (hc : 0 < c) :
    criticalCTConstant *
        (Real.exp (3 * criticalBlockTiltRate c) - 1) = c / 2 := by
  have hC : 0 < criticalCTConstant := by norm_num [criticalCTConstant]
  have hz : 0 < 1 + c / (2 * criticalCTConstant) := by positivity
  rw [criticalBlockTiltRate]
  have hthree : 3 * (Real.log (1 + c / (2 * criticalCTConstant)) / 3) =
      Real.log (1 + c / (2 * criticalCTConstant)) := by ring
  rw [hthree, Real.exp_log hz]
  field_simp [ne_of_gt hC]
  ring

/-- Fine-lattice tilt corresponding to a fixed block-scale rate. -/
noncomputable def criticalFineTiltRate (c : ℝ) (L : ℕ) : ℝ :=
  criticalBlockTiltRate c / (L : ℝ)

theorem criticalFineTiltRate_pos {c : ℝ} (hc : 0 < c)
    (L : ℕ) [NeZero L] :
    0 < criticalFineTiltRate c L := by
  exact div_pos (criticalBlockTiltRate_pos hc) (by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L))

/-- The growing fine-metric range and shrinking fine tilt have an exactly
constant product. -/
theorem criticalFineTiltRate_mul_range {c : ℝ} (L : ℕ) [NeZero L] :
    criticalFineTiltRate c L * (3 * L : ℕ) =
      3 * criticalBlockTiltRate c := by
  have hL : (L : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne L
  rw [criticalFineTiltRate]
  push_cast
  field_simp [hL]

/-- Uniform CT budget from any nonnegative kernel-times-ball product bounded
by `criticalCTConstant`. -/
theorem criticalScale_tiltBudget
    {c MN : ℝ} (hc : 0 < c)
    (hMN : MN ≤ criticalCTConstant)
    (L : ℕ) [NeZero L] :
    MN * (Real.exp (criticalFineTiltRate c L * (3 * L : ℕ)) - 1) ≤ c / 2 := by
  rw [criticalFineTiltRate_mul_range]
  have hrate := criticalBlockTiltRate_pos hc
  have hexp : 0 ≤ Real.exp (3 * criticalBlockTiltRate c) - 1 := by
    have : 1 ≤ Real.exp (3 * criticalBlockTiltRate c) := by
      rw [← Real.exp_zero]
      exact Real.exp_le_exp.mpr (by positivity)
    linarith
  calc
    MN * (Real.exp (3 * criticalBlockTiltRate c) - 1)
        ≤ criticalCTConstant *
            (Real.exp (3 * criticalBlockTiltRate c) - 1) :=
      mul_le_mul_of_nonneg_right hMN hexp
    _ = c / 2 := criticalBlockTiltRate_budget_eq hc

end YangMills.RG
