/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99OneScaleBlockPoincare

/-!
# Localized one-step estimate for the CMP99 multiscale Poincare induction

The global one-scale Poincare theorem is not by itself sufficient on the
nested source regions in CMP99 (3.24).  The proof is blockwise, however, and
therefore localizes to every finite family of coarse blocks.  This file
exposes that source-faithful form with the same explicit constants and no
ambient-volume factor.
-/

namespace YangMills.RG

open YangMills
open scoped BigOperators RealInnerProductSpace

noncomputable section

variable {d M N' Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero N'] [NeZero Nc]

/-- The derivative coefficient in the literal one-block estimate. -/
noncomputable def cmp99OneScaleBlockDerivativeCoefficient (d M : ℕ) : ℝ :=
  6 * (M : ℝ) ^ d * (((d * (M - 1) : ℕ) : ℝ) ^ 2)

/-- The average coefficient in the literal one-block estimate. -/
noncomputable def cmp99OneScaleBlockAverageCoefficient (d M : ℕ) : ℝ :=
  3 * (M : ℝ) ^ d

/-- L1 in coefficient-sharp form: one-step Poincare summed over an arbitrary
physical family of coarse blocks. -/
theorem sum_norm_sq_sourceBlocks_le_covariantEnergy_add_average
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (phi : PhysicalGaugeZeroCochain d (M * N') Nc)
    (K : Finset (FinBox d N')) :
    (∑ y ∈ K,
      ∑ x : {x : FinBox d (M * N') // x ∈ blockOf M N' y},
        ‖phi x.1‖ ^ 2) ≤
      cmp99OneScaleBlockDerivativeCoefficient d M *
          (∑ y ∈ K, cmp99BlockCovariantEnergy rho U phi y) +
        cmp99OneScaleBlockAverageCoefficient d M *
          (∑ y ∈ K,
            ‖cmp99FullSourceBlockAverageValue rho U phi y‖ ^ 2) := by
  calc
    (∑ y ∈ K,
      ∑ x : {x : FinBox d (M * N') // x ∈ blockOf M N' y},
        ‖phi x.1‖ ^ 2) ≤
      ∑ y ∈ K,
        (cmp99OneScaleBlockDerivativeCoefficient d M *
            cmp99BlockCovariantEnergy rho U phi y +
          cmp99OneScaleBlockAverageCoefficient d M *
            ‖cmp99FullSourceBlockAverageValue rho U phi y‖ ^ 2) := by
      apply Finset.sum_le_sum
      intro y _hy
      simpa [cmp99OneScaleBlockDerivativeCoefficient,
        cmp99OneScaleBlockAverageCoefficient, mul_assoc] using
        sum_norm_sq_block_le_covariantEnergy_add_average rho U phi y
    _ = cmp99OneScaleBlockDerivativeCoefficient d M *
          (∑ y ∈ K, cmp99BlockCovariantEnergy rho U phi y) +
        cmp99OneScaleBlockAverageCoefficient d M *
          (∑ y ∈ K,
            ‖cmp99FullSourceBlockAverageValue rho U phi y‖ ^ 2) := by
      simp only [Finset.sum_add_distrib, Finset.mul_sum]

/-- L1 in the uniform max-coefficient form used by the multiscale induction.
The constant is exactly the already-audited one-scale source constant. -/
theorem sum_norm_sq_sourceBlocks_le_cmp99OneScaleBlockPoincare
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (phi : PhysicalGaugeZeroCochain d (M * N') Nc)
    (K : Finset (FinBox d N')) :
    (∑ y ∈ K,
      ∑ x : {x : FinBox d (M * N') // x ∈ blockOf M N' y},
        ‖phi x.1‖ ^ 2) ≤
      cmp99OneScaleBlockPoincareConstant d M *
        ((∑ y ∈ K, cmp99BlockCovariantEnergy rho U phi y) +
          ∑ y ∈ K,
            ‖cmp99FullSourceBlockAverageValue rho U phi y‖ ^ 2) := by
  have h := sum_norm_sq_sourceBlocks_le_covariantEnergy_add_average
    rho U phi K
  let A := cmp99OneScaleBlockDerivativeCoefficient d M
  let B := cmp99OneScaleBlockAverageCoefficient d M
  let E := ∑ y ∈ K, cmp99BlockCovariantEnergy rho U phi y
  let Q := ∑ y ∈ K,
    ‖cmp99FullSourceBlockAverageValue rho U phi y‖ ^ 2
  have hE : 0 ≤ E := by
    dsimp only [E]
    exact Finset.sum_nonneg fun y _ =>
      cmp99BlockCovariantEnergy_nonneg rho U phi y
  have hQ : 0 ≤ Q := by
    dsimp only [Q]
    positivity
  have hA : A ≤ cmp99OneScaleBlockPoincareConstant d M := by
    exact le_max_left _ _
  have hB : B ≤ cmp99OneScaleBlockPoincareConstant d M := by
    exact le_max_right _ _
  change _ ≤ A * E + B * Q at h
  change _ ≤ cmp99OneScaleBlockPoincareConstant d M * (E + Q)
  calc
    _ ≤ A * E + B * Q := h
    _ ≤ cmp99OneScaleBlockPoincareConstant d M * E +
        cmp99OneScaleBlockPoincareConstant d M * Q :=
      add_le_add
        (mul_le_mul_of_nonneg_right hA hE)
        (mul_le_mul_of_nonneg_right hB hQ)
    _ = cmp99OneScaleBlockPoincareConstant d M * (E + Q) := by ring

end

end YangMills.RG
