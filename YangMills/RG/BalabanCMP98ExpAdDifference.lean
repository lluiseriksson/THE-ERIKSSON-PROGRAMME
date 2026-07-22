/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP98ExpDividedDifference

/-!
# The summed exponential divided-difference identity

Summing the finite identity term by term gives

`(ad Y) * D exp(Y) = sum n, (L_Y^n - R_Y^n)/n!`.

The right-hand side is the operator form of `exp(L_Y) - exp(R_Y)`.
This theorem is deliberately valid even when `ad Y` is singular; no
cancellation or inverse is used.
-/

namespace YangMills.RG

open scoped BigOperators RightActions

noncomputable section

variable {𝔸 : Type*}
variable [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]

/-- Absolute summability of the complete ordered exponential derivative. -/
theorem summable_expTermFDeriv [NormOneClass 𝔸] (Y : 𝔸) :
    Summable (expTermFDeriv Y) := by
  exact
    (summable_natCast_div_factorial_mul_pow_pred ‖Y‖).of_norm_bounded
      (fun n => norm_expTermFDeriv_le Y n)

/-- The operator-valued exponential divided difference. -/
def cmp98ExpAdDifference (Y : 𝔸) : 𝔸 →L[ℝ] 𝔸 :=
  ∑' n : ℕ, ((n.factorial : ℝ)⁻¹) •
    ((cmp98LeftMulCLM Y) ^ n - (cmp98RightMulCLM Y) ^ n)

/-- The difference series is summable because it is termwise the continuous
left-multiplication image of the ordered derivative series. -/
theorem summable_cmp98ExpAdDifference_term [NormOneClass 𝔸] (Y : 𝔸) :
    Summable (fun n : ℕ => ((n.factorial : ℝ)⁻¹) •
      ((cmp98LeftMulCLM Y) ^ n - (cmp98RightMulCLM Y) ^ n)) := by
  have hmaj :=
    (summable_natCast_div_factorial_mul_pow_pred ‖Y‖).mul_left (2 * ‖Y‖)
  apply hmaj.of_norm_bounded
  intro n
  rw [← cmp98AdCLM_mul_expTermFDeriv]
  calc
    ‖cmp98AdCLM Y * expTermFDeriv Y n‖ ≤
        ‖cmp98AdCLM Y‖ * ‖expTermFDeriv Y n‖ := norm_mul_le _ _
    _ ≤ (2 * ‖Y‖) *
        (((n : ℝ) / n.factorial) * ‖Y‖ ^ n.pred) := by
      gcongr
      · exact norm_cmp98AdCLM_le Y
      · exact norm_expTermFDeriv_le Y n

/-- Summed, cancellation-free form of CMP98's basic exponential identity. -/
theorem cmp98AdCLM_mul_fderiv_exp [NormOneClass 𝔸] (Y : 𝔸) :
    cmp98AdCLM Y * fderiv ℝ (NormedSpace.exp : 𝔸 → 𝔸) Y =
      cmp98ExpAdDifference Y := by
  rw [fderiv_exp_eq_ordered, cmp98ExpAdDifference]
  have hs := summable_expTermFDeriv Y
  have hd := summable_cmp98ExpAdDifference_term Y
  ext H
  let evalH : (𝔸 →L[ℝ] 𝔸) →L[ℝ] 𝔸 :=
    ContinuousLinearMap.apply ℝ 𝔸 H
  let leftEval : (𝔸 →L[ℝ] 𝔸) →L[ℝ] 𝔸 :=
    (cmp98AdCLM Y).comp evalH
  calc
    (cmp98AdCLM Y * ∑' n : ℕ, expTermFDeriv Y n) H =
        leftEval (∑' n : ℕ, expTermFDeriv Y n) := by
          rfl
    _ = ∑' n : ℕ, leftEval (expTermFDeriv Y n) :=
      leftEval.map_tsum hs
    _ = ∑' n : ℕ, evalH
        (((n.factorial : ℝ)⁻¹) •
          ((cmp98LeftMulCLM Y) ^ n - (cmp98RightMulCLM Y) ^ n)) := by
      apply tsum_congr
      intro n
      exact congrArg (fun T : 𝔸 →L[ℝ] 𝔸 => T H)
        (cmp98AdCLM_mul_expTermFDeriv Y n)
    _ = (∑' n : ℕ, ((n.factorial : ℝ)⁻¹) •
        ((cmp98LeftMulCLM Y) ^ n - (cmp98RightMulCLM Y) ^ n)) H := by
      exact (evalH.map_tsum hd).symm

/-- Pointwise form of the summed divided-difference identity. -/
theorem cmp98AdCLM_fderiv_exp_apply [NormOneClass 𝔸] (Y H : 𝔸) :
    cmp98AdCLM Y (fderiv ℝ (NormedSpace.exp : 𝔸 → 𝔸) Y H) =
      cmp98ExpAdDifference Y H := by
  have h := congrArg (fun T : 𝔸 →L[ℝ] 𝔸 => T H)
    (cmp98AdCLM_mul_fderiv_exp Y)
  simpa [ContinuousLinearMap.mul_apply] using h

end

end YangMills.RG
