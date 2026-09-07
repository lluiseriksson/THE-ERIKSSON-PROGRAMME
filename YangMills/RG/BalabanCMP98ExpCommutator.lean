/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP98ExpAdDifference

/-!
# The exponential commutator identity

The operator series on the right of the summed divided-difference identity
acts pointwise as

`H |-> exp(Y) H - H exp(Y)`.

Consequently

`(ad Y) (D exp(Y) H) = exp(Y) H - H exp(Y)`.

This is the exact cancellation-free identity underlying CMP98 (32).
-/

namespace YangMills.RG

open scoped BigOperators RightActions

noncomputable section

variable {𝔸 : Type*}
variable [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]

/-- The left part of the exponential difference has the expected sum. -/
theorem hasSum_exp_pow_mul_right (Y H : 𝔸) :
    HasSum (fun n : ℕ => ((n.factorial : ℝ)⁻¹) • (Y ^ n * H))
      (NormedSpace.exp Y * H) := by
  let rightH : 𝔸 →L[ℝ] 𝔸 := ContinuousLinearMap.id ℝ 𝔸 <• H
  have h := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) Y).map
    rightH rightH.continuous
  convert h using 1
  funext n
  simp [rightH, Function.comp_apply]

/-- The right part of the exponential difference has the expected sum. -/
theorem hasSum_mul_left_exp_pow (Y H : 𝔸) :
    HasSum (fun n : ℕ => ((n.factorial : ℝ)⁻¹) • (H * Y ^ n))
      (H * NormedSpace.exp Y) := by
  let leftH : 𝔸 →L[ℝ] 𝔸 := H •> ContinuousLinearMap.id ℝ 𝔸
  have h := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) Y).map
    leftH leftH.continuous
  convert h using 1
  funext n
  simp [leftH, Function.comp_apply]

/-- Pointwise evaluation of the operator-valued exponential difference. -/
theorem cmp98ExpAdDifference_apply_eq [NormOneClass 𝔸] (Y H : 𝔸) :
    cmp98ExpAdDifference Y H =
      NormedSpace.exp Y * H - H * NormedSpace.exp Y := by
  have hsum := (hasSum_exp_pow_mul_right Y H).sub
    (hasSum_mul_left_exp_pow Y H)
  have hsum' : HasSum
      (fun n : ℕ => ((n.factorial : ℝ)⁻¹) •
        (Y ^ n * H - H * Y ^ n))
      (NormedSpace.exp Y * H - H * NormedSpace.exp Y) := by
    simpa [smul_sub] using hsum
  have hterm (n : ℕ) :
      (((n.factorial : ℝ)⁻¹) •
        ((cmp98LeftMulCLM Y) ^ n - (cmp98RightMulCLM Y) ^ n)) H =
        ((n.factorial : ℝ)⁻¹) • (Y ^ n * H - H * Y ^ n) := by
    rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply,
      cmp98LeftMulCLM_pow_apply, cmp98RightMulCLM_pow_apply]
  unfold cmp98ExpAdDifference
  have hd := summable_cmp98ExpAdDifference_term (Y := Y)
  let evalH : (𝔸 →L[ℝ] 𝔸) →L[ℝ] 𝔸 :=
    ContinuousLinearMap.apply ℝ 𝔸 H
  calc
    (∑' n : ℕ, ((n.factorial : ℝ)⁻¹) •
        ((cmp98LeftMulCLM Y) ^ n - (cmp98RightMulCLM Y) ^ n)) H =
        evalH (∑' n : ℕ, ((n.factorial : ℝ)⁻¹) •
          ((cmp98LeftMulCLM Y) ^ n - (cmp98RightMulCLM Y) ^ n)) := rfl
    _ = ∑' n : ℕ, evalH (((n.factorial : ℝ)⁻¹) •
          ((cmp98LeftMulCLM Y) ^ n - (cmp98RightMulCLM Y) ^ n)) :=
      evalH.map_tsum hd
    _ = ∑' n : ℕ, ((n.factorial : ℝ)⁻¹) •
          (Y ^ n * H - H * Y ^ n) := by
      apply tsum_congr
      intro n
      exact hterm n
    _ = NormedSpace.exp Y * H - H * NormedSpace.exp Y := hsum'.tsum_eq

/-- The exact exponential commutator formula in an arbitrary real Banach
algebra. -/
theorem cmp98AdCLM_fderiv_exp_eq_exp_commutator [NormOneClass 𝔸]
    (Y H : 𝔸) :
    cmp98AdCLM Y (fderiv ℝ (NormedSpace.exp : 𝔸 → 𝔸) Y H) =
      NormedSpace.exp Y * H - H * NormedSpace.exp Y := by
  rw [cmp98AdCLM_fderiv_exp_apply, cmp98ExpAdDifference_apply_eq]

end

end YangMills.RG
