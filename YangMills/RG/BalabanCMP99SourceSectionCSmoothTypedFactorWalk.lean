/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceSectionCTypedFactorWalk
import YangMills.RG.BalabanCMP99SourceGeneratedSectionCSmoothCommutatorFactor

/-!
# CMP95-generated interpretation of the typed CMP99 Section C labels

This module removes the last free cutoff datum from the reconstructed label
interpreter. A single CMP95 (1.118) profile generates the exact periodic
coarse square partition used by every cut factor and the source-centred smooth
cutoff used in the printed same-scale commutator factor on CMP99 p. 412.

The open `Other` family stays empty here. Consequently this is an exact
interpreter of the two source species already reconstructed, not a claim that
the paper's non-exhaustive word "etc." has been enumerated.
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
set_option maxHeartbeats 6000000

/-- Interpret the two reconstructed typed species from one CMP95 source
profile. Cut labels use its exact periodic square partition; commutator
labels use its source-centred smooth `M0^-1` realization. -/
noncomputable def generatedCMP95SectionCSourceLabelOperator
    (D : CMP99SourceDependentOmegaGeometry
      (FinBox 4 (2 * Q)) j ScaleSite Scaled
      (cmp99SourceTildePiLargeBlocks cell 3)
      (cmp99SourceTildePiLargeBlocks cell 4) dist gap)
    (P : CMP95SourceSmoothPartitionProfile)
    (hpi5 : D.fineRegion (cmp99OmegaZeroIndex j) ⊆
      cmp99SourceTildePiLargeBlocks cell 5)
    (hM : 2 ≤ M) (depth : ℕ)
    {spacing epsilon : ℝ} (hspacing : 0 < spacing)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 M Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff 4 M (depth + 1)
      spacing epsilon < 1)
    {r s : Fin (j + 2)} :
    CMP99SectionCTypedFactorLabel j (fun _ _ => Empty) r s →
      DependentFinitePiLpArrow (D.GeneratedSectionCCoarseSiteFamily hpi5)
        (SUNLieCoord Nc) r s
  | .cut k =>
      D.generatedSectionCCutTowerStep hpi5
        (fun t => D.generatedSectionCSourceTransitionCutData
          (cmp95SourcePeriodicCoarseSquarePartition P Q) hpi5 t)
        hM depth hspacing background budget fineSmall hsmall k
  | .commutator t =>
      D.generatedCMP95SourceCenteredSectionCCommutatorFactorCoordinates P
        hpi5 t hM depth hspacing background budget fineSmall hsmall
  | .other alpha => nomatch alpha

@[simp] theorem generatedCMP95SectionCSourceLabelOperator_cut
    (D : CMP99SourceDependentOmegaGeometry
      (FinBox 4 (2 * Q)) j ScaleSite Scaled
      (cmp99SourceTildePiLargeBlocks cell 3)
      (cmp99SourceTildePiLargeBlocks cell 4) dist gap)
    (P : CMP95SourceSmoothPartitionProfile)
    (hpi5 : D.fineRegion (cmp99OmegaZeroIndex j) ⊆
      cmp99SourceTildePiLargeBlocks cell 5)
    (hM : 2 ≤ M) (depth : ℕ)
    {spacing epsilon : ℝ} (hspacing : 0 < spacing)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 M Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff 4 M (depth + 1)
      spacing epsilon < 1)
    (r : Fin (j + 1)) :
    D.generatedCMP95SectionCSourceLabelOperator P hpi5 hM depth hspacing
        background budget fineSmall hsmall
        (CMP99SectionCTypedFactorLabel.cut r) =
      D.generatedSectionCCutTowerStep hpi5
        (fun t => D.generatedSectionCSourceTransitionCutData
          (cmp95SourcePeriodicCoarseSquarePartition P Q) hpi5 t)
        hM depth hspacing background budget fineSmall hsmall r := rfl

@[simp] theorem generatedCMP95SectionCSourceLabelOperator_commutator
    (D : CMP99SourceDependentOmegaGeometry
      (FinBox 4 (2 * Q)) j ScaleSite Scaled
      (cmp99SourceTildePiLargeBlocks cell 3)
      (cmp99SourceTildePiLargeBlocks cell 4) dist gap)
    (P : CMP95SourceSmoothPartitionProfile)
    (hpi5 : D.fineRegion (cmp99OmegaZeroIndex j) ⊆
      cmp99SourceTildePiLargeBlocks cell 5)
    (hM : 2 ≤ M) (depth : ℕ)
    {spacing epsilon : ℝ} (hspacing : 0 < spacing)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 M Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff 4 M (depth + 1)
      spacing epsilon < 1)
    (s : Fin (j + 2)) :
    D.generatedCMP95SectionCSourceLabelOperator P hpi5 hM depth hspacing
        background budget fineSmall hsmall
        (CMP99SectionCTypedFactorLabel.commutator s) =
      D.generatedCMP95SourceCenteredSectionCCommutatorFactorCoordinates P
        hpi5 s hM depth hspacing background budget fineSmall hsmall := rfl

/-- Interpret any well-typed walk over the two reconstructed source species.
The dependent endpoints prevent inserting a factor at the wrong scale. -/
noncomputable def generatedCMP95SectionCSourceOperatorWalk
    (D : CMP99SourceDependentOmegaGeometry
      (FinBox 4 (2 * Q)) j ScaleSite Scaled
      (cmp99SourceTildePiLargeBlocks cell 3)
      (cmp99SourceTildePiLargeBlocks cell 4) dist gap)
    (P : CMP95SourceSmoothPartitionProfile)
    (hpi5 : D.fineRegion (cmp99OmegaZeroIndex j) ⊆
      cmp99SourceTildePiLargeBlocks cell 5)
    (hM : 2 ≤ M) (depth : ℕ)
    {spacing epsilon : ℝ} (hspacing : 0 < spacing)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 M Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff 4 M (depth + 1)
      spacing epsilon < 1)
    {r s : Fin (j + 2)}
    (walk : DependentArrowWalk
      (CMP99SectionCTypedFactorLabel j (fun _ _ => Empty)) r s) :=
  walk.map (D.generatedCMP95SectionCSourceLabelOperator P hpi5 hM depth
    hspacing background budget fineSmall hsmall)

end CMP99SourceDependentOmegaGeometry

end

end YangMills.RG
