/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP102PhysicalBlockDerivativeBackgroundLipschitz

/-!
# Background Lipschitz control of the CMP98 right variation

This module closes the source-level comparison needed by the CMP109 pivot.
It combines the two physical factors already constructed:

* the literal derivative of the nonlinear CMP98 block;
* the literal right inverse `C(U)† exp(-Y(U))`.

The result controls the difference of the actual right-trivialized
variations, not a surrogate matrix supplied by the caller.  Its only field
factor is the unrestricted CMP109 tangent norm and its coefficient is
independent of the periodic volume.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {d M N' Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero N'] [NeZero Nc]

local instance cmp102PhysicalRightVariationBackgroundMatrixNormOneClass :
    NormOneClass (Matrix (Fin Nc) (Fin Nc) ℂ) where
  norm_one := by
    rw [← Matrix.diagonal_one, Matrix.l2_opNorm_diagonal]
    simp

/-- Generated coefficient for the small-background difference of the actual
CMP98 nonlinear right variation. -/
def cmp102PhysicalRightVariationBackgroundBudget
    (d M : ℕ) (r ε : ℝ) : ℝ :=
  cmp102PhysicalBlockDerivativeBackgroundBudget d M r ε *
      cmp98SourceOuterExpNormBudget r +
    cmp102PhysicalBlockDerivativeLinearBudget d M r *
      cmp102PhysicalRightInverseBackgroundBudget d M r ε

theorem cmp102PhysicalRightVariationBackgroundBudget_nonneg
    {d M : ℕ} {r ε : ℝ} (hr : 0 ≤ r) (hε : 0 ≤ ε) :
    0 ≤ cmp102PhysicalRightVariationBackgroundBudget d M r ε := by
  unfold cmp102PhysicalRightVariationBackgroundBudget
  exact add_nonneg
    (mul_nonneg
      (cmp102PhysicalBlockDerivativeBackgroundBudget_nonneg hr hε)
      (cmp98SourceOuterExpNormBudget_nonneg_of_nonneg hr))
    (mul_nonneg
      (cmp102PhysicalBlockDerivativeLinearBudget_nonneg hr)
      (cmp102PhysicalRightInverseBackgroundBudget_nonneg hr hε))

/-- The represented derivative followed by its right inverse is exactly the
literal nonlinear right variation. -/
theorem cmp98Eq119NonlinearRightVariation_eq_blockPhysicalVariation_mul_inverse
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N')
    (hsmall : ∀ x ∈ blockOf M N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix U b x 0‖ < 1) :
    cmp98Eq119NonlinearRightVariation U A b =
      cmp98Eq119NonlinearBlockPhysicalVariation U A b *
        cmp98Eq119NonlinearBlockInverseAtZero U A b := by
  unfold cmp98Eq119NonlinearRightVariation
  rw [(hasDerivAt_cmp98Eq119NonlinearBlockCurve U A b hsmall).deriv,
    cmp98Eq119_fourFactorFirst_eq]
  rfl

/-- **Physical CMP98 background response bound.**  The actual nonlinear right
variation differs from its flat-background value by an explicit
volume-independent multiple of the inserted CMP109 tangent. -/
theorem
    norm_cmp98Eq119NonlinearRightVariation_sub_trivial_le_sourceScale
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (ε r : ℝ) (hε : 0 ≤ ε) (hr13 : 1 / 3 ≤ r) (hr1 : r < 1)
    (hsmall : PhysicalWilsonSmallBackground U ε)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N')
    (hbaseU : ∀ x ∈ blockOf M N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix U b x 0‖ ≤ 1 / 3)
    (hbase0 : ∀ x ∈ blockOf M N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix
        (trivialPhysicalGaugeBackground d (M * N') Nc) b x 0‖ ≤ 1 / 3) :
    ‖cmp98Eq119NonlinearRightVariation U A b -
        cmp98Eq119NonlinearRightVariation
          (trivialPhysicalGaugeBackground d (M * N') Nc) A b‖ ≤
      cmp102PhysicalRightVariationBackgroundBudget d M r ε *
        cmp98SourceFieldSupNorm A := by
  let U0 := trivialPhysicalGaugeBackground d (M * N') Nc
  let FU := cmp98Eq119NonlinearBlockPhysicalVariation U A b
  let F0 := cmp98Eq119NonlinearBlockPhysicalVariation U0 A b
  let IU := cmp98Eq119NonlinearBlockInverseAtZero U A b
  let I0 := cmp98Eq119NonlinearBlockInverseAtZero U0 A b
  let O := cmp98SourceOuterExpNormBudget r
  let S := cmp98SourceFieldSupNorm A
  have hsmallU : ∀ x ∈ blockOf M N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix U b x 0‖ < 1 :=
    fun x hx => (hbaseU x hx).trans_lt (by norm_num)
  have hsmall0 : ∀ x ∈ blockOf M N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix U0 b x 0‖ < 1 :=
    fun x hx => (hbase0 x hx).trans_lt (by norm_num)
  have hFUdiff : ‖FU - F0‖ ≤
      cmp102PhysicalBlockDerivativeBackgroundBudget d M r ε * S := by
    simpa only [FU, F0, U0, S] using
      norm_cmp98Eq119NonlinearBlockPhysicalVariation_sub_trivial_le_sourceScale
        U ε r hε hr13 hr1 hsmall A b hbaseU hbase0
  have hIU : ‖IU‖ ≤ O := by
    simpa only [IU, O] using
      norm_cmp98Eq119NonlinearBlockInverseAtZero_le_sourceBudget
        U A b r hbaseU hr13 hr1
  have hF0 : ‖F0‖ ≤
      cmp102PhysicalBlockDerivativeLinearBudget d M r * S := by
    simpa only [F0, U0, S] using
      norm_cmp98Eq119NonlinearBlockPhysicalVariation_le_sourceScale
        U0 A b r hbase0 hr13 hr1
  have hIdiff : ‖IU - I0‖ ≤
      cmp102PhysicalRightInverseBackgroundBudget d M r ε := by
    simpa only [IU, I0, U0] using
      norm_cmp98Eq119NonlinearBlockInverseAtZero_sub_trivial_le_sourceScale
        U ε r hε hr13 hr1 hsmall A b hbaseU hbase0
  have halg : FU * IU - F0 * I0 = (FU - F0) * IU + F0 * (IU - I0) := by
    noncomm_ring
  rw [cmp98Eq119NonlinearRightVariation_eq_blockPhysicalVariation_mul_inverse
      U A b hsmallU,
    cmp98Eq119NonlinearRightVariation_eq_blockPhysicalVariation_mul_inverse
      U0 A b hsmall0]
  change ‖FU * IU - F0 * I0‖ ≤ _
  rw [halg]
  calc
    ‖(FU - F0) * IU + F0 * (IU - I0)‖
        ≤ ‖FU - F0‖ * ‖IU‖ + ‖F0‖ * ‖IU - I0‖ := by
      exact (norm_add_le _ _).trans
        (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))
    _ ≤
        (cmp102PhysicalBlockDerivativeBackgroundBudget d M r ε * S) * O +
          (cmp102PhysicalBlockDerivativeLinearBudget d M r * S) *
            cmp102PhysicalRightInverseBackgroundBudget d M r ε := by
      exact add_le_add
        (mul_le_mul hFUdiff hIU (norm_nonneg IU)
          (mul_nonneg
            (cmp102PhysicalBlockDerivativeBackgroundBudget_nonneg
              ((by norm_num : (0 : ℝ) ≤ 1 / 3).trans hr13) hε)
            (cmp98SourceFieldSupNorm_nonneg A)))
        (mul_le_mul hF0 hIdiff (norm_nonneg (IU - I0))
          (mul_nonneg
            (cmp102PhysicalBlockDerivativeLinearBudget_nonneg
              ((by norm_num : (0 : ℝ) ≤ 1 / 3).trans hr13))
            (cmp98SourceFieldSupNorm_nonneg A)))
    _ = cmp102PhysicalRightVariationBackgroundBudget d M r ε * S := by
      unfold cmp102PhysicalRightVariationBackgroundBudget O
      ring

end

end YangMills.RG
