/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceGeneratedCoarseCovarianceTransition

/-!
# Uniform norm of the generated CMP99 coarse-covariance transition

The complete terminal restriction is contractive and each generated coarse
covariance inherits the inverse-coercivity norm bound.  Their rectangular
mismatch is therefore uniformly bounded without any ambient-volume or tower-
depth factor.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator RealInnerProductSpace

noncomputable section

variable {d M N Nc : ℕ} [NeZero d] [NeZero M] [NeZero N] [NeZero Nc]

/-- Operator norm of one complete generated coarse covariance. -/
theorem norm_cmp99SourceGeneratedPhysicalCoarseCovariance_le
    (hd : 2 ≤ d) (hM : 2 ≤ M) (Omega : ActiveGaugeRegion d N)
    (depth : ℕ) {spacing epsilon : ℝ} (hspacing : 0 < spacing)
    (background : GaugeConfig d
      (cmp99RegionalLatticeSize M N (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget d M Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge d
      (cmp99RegionalLatticeSize M N (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff d M (depth + 1)
      spacing epsilon < 1) :
    ‖cmp99SourceGeneratedPhysicalCoarseCovariance hd hM Omega depth hspacing
      background budget fineSmall hsmall‖ ≤
      (((cmp99SourceGeneratedPhysicalPrecisionUpperBound d M (depth + 1)
        spacing epsilon) ^ 2)⁻¹)⁻¹ := by
  exact norm_covarianceOfIsCoerciveCLM_le _
    (inv_pos.mpr (sq_pos_of_pos
      (cmp99SourceGeneratedPhysicalPrecisionUpperBound_pos d M (depth + 1)
        hspacing)))
    (isCoerciveCLM_cmp99SourceGeneratedPhysicalCoarseCovarianceMiddle hd hM
      Omega depth hspacing background budget fineSmall hsmall)

/-- Explicit volume-independent amplitude for a consecutive generated coarse
covariance mismatch. -/
noncomputable def cmp99SourceGeneratedPhysicalCoarseCovarianceTransitionNormBound
    (d M depth : ℕ) (spacing epsilon : ℝ) : ℝ :=
  2 * (((cmp99SourceGeneratedPhysicalPrecisionUpperBound d M (depth + 1)
    spacing epsilon) ^ 2)⁻¹)⁻¹

universe v

namespace CMP99SourceDependentOmegaGeometry

variable {Q j : ℕ} [NeZero Q]
variable {cell : FinBox 4 Q}
variable {ScaleSite : Fin (j + 2) → Type v}
variable [∀ r, DecidableEq (ScaleSite r)]
variable {Scaled : CMP99SourceScaledStratification
  (FinBox 4 (2 * Q)) (j + 2) ScaleSite}
variable {dist : FinBox 4 (2 * Q) → FinBox 4 (2 * Q) → ℕ}
variable {gap : Fin (j + 1) → ℕ}

/- Uniform norm bound for the literal rectangular generated coarse-
covariance transition. -/
set_option maxRecDepth 2000 in
theorem norm_generatedPhysicalCoarseCovarianceTransition_le
    (D : CMP99SourceDependentOmegaGeometry
      (FinBox 4 (2 * Q)) j ScaleSite Scaled
      (cmp99SourceTildePiLargeBlocks cell 3)
      (cmp99SourceTildePiLargeBlocks cell 4) dist gap)
    (hpi5 : D.fineRegion (cmp99OmegaZeroIndex j) ⊆
      cmp99SourceTildePiLargeBlocks cell 5)
    (r : Fin (j + 1)) (hM : 2 ≤ M) (depth : ℕ)
    {spacing epsilon : ℝ} (hspacing : 0 < spacing)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 M Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff 4 M (depth + 1)
      spacing epsilon < 1) :
    ‖D.generatedPhysicalCoarseCovarianceTransition hpi5 r hM depth hspacing
      background budget fineSmall hsmall‖ ≤
      cmp99SourceGeneratedPhysicalCoarseCovarianceTransitionNormBound
        4 M depth spacing epsilon := by
  let Csmall := cmp99SourceGeneratedPhysicalCoarseCovariance
    (show 2 ≤ 4 by norm_num) hM
    (D.operatorCoarseRegion hpi5 (cmp99OmegaTransitionNextIndex r)) depth
    hspacing background budget fineSmall hsmall
  let Clarge := cmp99SourceGeneratedPhysicalCoarseCovariance
    (show 2 ≤ 4 by norm_num) hM
    (D.operatorCoarseRegion hpi5 (cmp99OmegaTransitionIndex r)) depth
    hspacing background budget fineSmall hsmall
  let R := D.generatedTerminalRestriction hpi5 r hM depth spacing epsilon
    background budget fineSmall
  let L := (((cmp99SourceGeneratedPhysicalPrecisionUpperBound
    4 M (depth + 1) spacing epsilon) ^ 2)⁻¹)⁻¹
  have hCsmall : ‖Csmall‖ ≤ L :=
    norm_cmp99SourceGeneratedPhysicalCoarseCovariance_le
      (show 2 ≤ 4 by norm_num) hM
      (D.operatorCoarseRegion hpi5 (cmp99OmegaTransitionNextIndex r)) depth
      hspacing background budget fineSmall hsmall
  have hClarge : ‖Clarge‖ ≤ L :=
    norm_cmp99SourceGeneratedPhysicalCoarseCovariance_le
      (show 2 ≤ 4 by norm_num) hM
      (D.operatorCoarseRegion hpi5 (cmp99OmegaTransitionIndex r)) depth
      hspacing background budget fineSmall hsmall
  have hR : ‖R‖ ≤ 1 :=
    D.norm_generatedTerminalRestriction_le_one hpi5 r hM depth spacing
      epsilon background budget fineSmall
  have hL : 0 ≤ L := by
    dsimp [L]
    positivity
  unfold generatedPhysicalCoarseCovarianceTransition
  change ‖Csmall.comp R - R.comp Clarge‖ ≤ 2 * L
  calc
    ‖Csmall.comp R - R.comp Clarge‖ ≤
        ‖Csmall.comp R‖ + ‖R.comp Clarge‖ := norm_sub_le _ _
    _ ≤ ‖Csmall‖ * ‖R‖ + ‖R‖ * ‖Clarge‖ :=
      add_le_add (ContinuousLinearMap.opNorm_comp_le _ _)
        (ContinuousLinearMap.opNorm_comp_le _ _)
    _ ≤ L * 1 + 1 * L :=
      add_le_add
        (mul_le_mul hCsmall hR (norm_nonneg _) hL)
        (mul_le_mul hR hClarge (norm_nonneg _) zero_le_one)
    _ = 2 * L := by ring

end CMP99SourceDependentOmegaGeometry

end

end YangMills.RG
