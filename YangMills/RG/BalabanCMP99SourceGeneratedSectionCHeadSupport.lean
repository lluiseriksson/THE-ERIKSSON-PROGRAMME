/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceGeneratedSectionCHeadFactor

/-!
# Exact source support of the CMP99 Section C covariance head

CMP95 printed p. 36, equation (1.118), chooses the one-dimensional profile
with support in `(-2/3, 2/3)`.  Its exact periodic regrouping therefore has a
literal cell support.  CMP99 printed p. 413 sandwiches the regional
covariance between two copies of that cutoff,

`R'_0(Pi) = h_Pi C_Pi h_Pi`.

This file proves the resulting bilateral kernel support.  It is stronger
than the previously available exponential estimate: a one-site matrix entry
is exactly zero when either endpoint lies outside the periodized source cell.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator RealInnerProductSpace

noncomputable section

universe v

variable {M Nc Q j : ℕ} [NeZero M] [NeZero Nc] [NeZero Q]
variable {cell : FinBox 4 Q}
variable {ScaleSite : Fin (j + 2) → Type v}
variable [∀ r, DecidableEq (ScaleSite r)]
variable {Scaled : CMP99SourceScaledStratification
  (FinBox 4 (2 * Q)) (j + 2) ScaleSite}
variable {dist : FinBox 4 (2 * Q) → FinBox 4 (2 * Q) → ℕ}
variable {gap : Fin (j + 1) → ℕ}

namespace CMP99SourceDependentOmegaGeometry

set_option maxRecDepth 3000
set_option maxHeartbeats 500000

/-- The literal covariance head vanishes at a target outside the periodized
source cell, independently of the covariance between the two cutoffs. -/
theorem generatedCMP95SectionCSourceHeadFactorCoordinates_apply_single_eq_zero_of_target
    (D : CMP99SourceDependentOmegaGeometry
      (FinBox 4 (2 * Q)) j ScaleSite Scaled
      (cmp99SourceTildePiLargeBlocks cell 3)
      (cmp99SourceTildePiLargeBlocks cell 4) dist gap)
    (P : CMP95SourceSmoothPartitionProfile)
    (hpi5 : D.fineRegion (cmp99OmegaZeroIndex j) ⊆
      cmp99SourceTildePiLargeBlocks cell 5)
    (s : Fin (j + 2)) (hM : 2 ≤ M) (depth : ℕ)
    {spacing epsilon : ℝ} (hspacing : 0 < spacing)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 M Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff 4 M (depth + 1)
      spacing epsilon < 1)
    (source target : ActiveGaugeRegion.Site (D.operatorCoarseRegion hpi5 s))
    (v : SUNLieCoord Nc)
    (houtside : ¬ cmp95SourcePeriodicCoarseCellSupport Q cell target.1) :
    D.generatedCMP95SectionCSourceHeadFactorCoordinates P hpi5 s hM depth
        hspacing background budget fineSmall hsmall
        (singleFinitePiLp source v) target = 0 := by
  have hzero :
      (cmp95SourcePeriodicCoarseSquarePartition P Q).value cell target.1 = 0 :=
    cmp95SourcePeriodicCoarseSquarePartition_value_eq_zero_of_not_support
      P Q cell target.1 houtside
  unfold generatedCMP95SectionCSourceHeadFactorCoordinates
  unfold generatedSectionCSourceHeadFactorCoordinates
  rw [ContinuousLinearMap.comp_apply, finitePiLpScalarMultiplier_apply,
    hzero, zero_smul]

/-- The literal covariance head also vanishes when its one-site source lies
outside the periodized source cell. -/
theorem generatedCMP95SectionCSourceHeadFactorCoordinates_apply_single_eq_zero_of_source
    (D : CMP99SourceDependentOmegaGeometry
      (FinBox 4 (2 * Q)) j ScaleSite Scaled
      (cmp99SourceTildePiLargeBlocks cell 3)
      (cmp99SourceTildePiLargeBlocks cell 4) dist gap)
    (P : CMP95SourceSmoothPartitionProfile)
    (hpi5 : D.fineRegion (cmp99OmegaZeroIndex j) ⊆
      cmp99SourceTildePiLargeBlocks cell 5)
    (s : Fin (j + 2)) (hM : 2 ≤ M) (depth : ℕ)
    {spacing epsilon : ℝ} (hspacing : 0 < spacing)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 M Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff 4 M (depth + 1)
      spacing epsilon < 1)
    (source target : ActiveGaugeRegion.Site (D.operatorCoarseRegion hpi5 s))
    (v : SUNLieCoord Nc)
    (houtside : ¬ cmp95SourcePeriodicCoarseCellSupport Q cell source.1) :
    D.generatedCMP95SectionCSourceHeadFactorCoordinates P hpi5 s hM depth
        hspacing background budget fineSmall hsmall
        (singleFinitePiLp source v) target = 0 := by
  have hzero :
      (cmp95SourcePeriodicCoarseSquarePartition P Q).value cell source.1 = 0 :=
    cmp95SourcePeriodicCoarseSquarePartition_value_eq_zero_of_not_support
      P Q cell source.1 houtside
  unfold generatedCMP95SectionCSourceHeadFactorCoordinates
  unfold generatedSectionCSourceHeadFactorCoordinates
  simp only [ContinuousLinearMap.comp_apply]
  rw [finitePiLpScalarMultiplier_single, hzero, zero_smul]
  have hsingle : singleFinitePiLp source (0 : SUNLieCoord Nc) = 0 := by
    apply PiLp.ext
    intro x
    by_cases hx : x = source
    · subst x
      simp
    · rw [singleFinitePiLp_of_ne (0 : SUNLieCoord Nc) hx]
      rfl
  rw [hsingle]
  simp

/-- Bilateral exact support of the CMP99 p. 413 head. -/
theorem generatedCMP95SectionCSourceHeadFactorCoordinates_apply_single_eq_zero_of_endpoint
    (D : CMP99SourceDependentOmegaGeometry
      (FinBox 4 (2 * Q)) j ScaleSite Scaled
      (cmp99SourceTildePiLargeBlocks cell 3)
      (cmp99SourceTildePiLargeBlocks cell 4) dist gap)
    (P : CMP95SourceSmoothPartitionProfile)
    (hpi5 : D.fineRegion (cmp99OmegaZeroIndex j) ⊆
      cmp99SourceTildePiLargeBlocks cell 5)
    (s : Fin (j + 2)) (hM : 2 ≤ M) (depth : ℕ)
    {spacing epsilon : ℝ} (hspacing : 0 < spacing)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 M Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff 4 M (depth + 1)
      spacing epsilon < 1)
    (source target : ActiveGaugeRegion.Site (D.operatorCoarseRegion hpi5 s))
    (v : SUNLieCoord Nc)
    (houtside :
      ¬ cmp95SourcePeriodicCoarseCellSupport Q cell source.1 ∨
      ¬ cmp95SourcePeriodicCoarseCellSupport Q cell target.1) :
    D.generatedCMP95SectionCSourceHeadFactorCoordinates P hpi5 s hM depth
        hspacing background budget fineSmall hsmall
        (singleFinitePiLp source v) target = 0 := by
  rcases houtside with hsource | htarget
  · exact D.generatedCMP95SectionCSourceHeadFactorCoordinates_apply_single_eq_zero_of_source
      P hpi5 s hM depth hspacing background budget fineSmall hsmall
        source target v hsource
  · exact D.generatedCMP95SectionCSourceHeadFactorCoordinates_apply_single_eq_zero_of_target
      P hpi5 s hM depth hspacing background budget fineSmall hsmall
        source target v htarget

end CMP99SourceDependentOmegaGeometry

end
end YangMills.RG
