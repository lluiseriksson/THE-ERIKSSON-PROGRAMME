/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP102PhysicalBackgroundCorrectionLipschitz

/-!
# Uniform source norm on the CMP102 correction ball

This module turns membership in the Banach ball for the unknown correction
`D` into the literal source-sup estimate

`|A - H D|∞ ≤ |A|∞ + ‖H‖∞ ρ`.

The norm of `H` is the constructed physical CMP99 source-sup operator norm;
no new boundedness certificate is supplied by the caller.
-/

namespace YangMills.RG

open YangMills

noncomputable section

variable {d L N' Nc : ℕ}
variable [NeZero d] [NeZero L] [NeZero N'] [NeZero Nc]
  [NeZero (L * N')]

/-- The finite source sup norm satisfies the triangle inequality for
subtraction. -/
theorem cmp98SourceFieldSupNorm_sub_le
    (A B : PhysicalGaugeOneCochain d (L * N') Nc) :
    cmp98SourceFieldSupNorm (A - B) ≤
      cmp98SourceFieldSupNorm A + cmp98SourceFieldSupNorm B := by
  classical
  unfold cmp98SourceFieldSupNorm
  apply (Finset.max'_le_iff _ _).2
  intro y hy
  rcases Finset.mem_image.mp hy with ⟨b, _, rfl⟩
  exact (norm_sub_le (A b) (B b)).trans
    (add_le_add
      (Finset.le_max' _ _ (by simp))
      (Finset.le_max' _ _ (by simp)))

set_option maxHeartbeats 3000000 in
/-- The physical CMP99 minimizer controls the whole shifted background on a
closed source-sup ball. -/
theorem cmp98SourceFieldSupNorm_physicalBackgroundShift_le
    (U : PhysicalGaugeBackground d (L * N') Nc)
    {a CP ε : ℝ} (ha : 0 < a)
    (hP : FlatGaugeHodgePoincare d L N' Nc
      (matrixSUNAdjointModel Nc) CP)
    (hε : 0 ≤ ε) (hsmall : PhysicalWilsonSmallBackground U ε)
    (hbudget : cmp116ConcreteInteractingWilsonGaugeDefectBudget d Nc ε <
      min 1 a / CP)
    (A : PhysicalGaugeOneCochain d (L * N') Nc)
    (D : PhysicalGaugeOneCochainSup d N' Nc)
    (ρ : ℝ) (hD : ‖D‖ ≤ ρ) :
    cmp98SourceFieldSupNorm
        (A - cmp99SourceEq3126PhysicalH U ha hP hε hsmall hbudget
          (physicalGaugeOneCochainSupEquiv.symm D)) ≤
      cmp98SourceFieldSupNorm A +
        cmp99SourceEq3126PhysicalHSourceSupNorm
            U ha hP hε hsmall hbudget * ρ := by
  have hH :=
    cmp98SourceFieldSupNorm_cmp99SourceEq3126PhysicalH_le
      U ha hP hε hsmall hbudget
      (physicalGaugeOneCochainSupEquiv.symm D)
  have hnorm :
      cmp102PhysicalCorrectionSupNorm
          (physicalGaugeOneCochainSupEquiv.symm D) = ‖D‖ := by
    rw [← norm_physicalGaugeOneCochainSupEquiv_eq_correctionSupNorm]
    simp
  rw [hnorm] at hH
  have hHnonneg :
      0 ≤ cmp99SourceEq3126PhysicalHSourceSupNorm
        U ha hP hε hsmall hbudget := norm_nonneg _
  exact (cmp98SourceFieldSupNorm_sub_le A _).trans
    (add_le_add (le_refl _)
      (hH.trans (mul_le_mul_of_nonneg_left hD hHnonneg)))

end

end YangMills.RG
