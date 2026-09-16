/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceGeneratedSectionCHeadedTypedWalk
import YangMills.RG.BalabanCMP99SourceGeneratedSectionCSmoothCommutatorFactor

/-!
# Identification of the CMP99 Section C covariance head

The p. 412 commutator species ends in `h_Pi C_Pi h_Pi`, while p. 413 names
that same operator `R'_0(Pi)`.  These theorems prove literal equality between
the tail already present in the full commutator factor and the independently
exposed head.  Consequently the headed walk does not introduce a parallel
copy of the covariance tail.
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

/-- The tail of the complete smooth p. 412 commutator factor is literally
the p. 413 head `R'_0(Pi)`. -/
theorem generatedPhysicalSmoothSectionCCommutatorFactorCoordinates_eq_head
    (D : CMP99SourceDependentOmegaGeometry
      (FinBox 4 (2 * Q)) j ScaleSite Scaled
      (cmp99SourceTildePiLargeBlocks cell 3)
      (cmp99SourceTildePiLargeBlocks cell 4) dist gap)
    (fineProfile : CMP95SourceSmoothPartitionProfile)
    (coarsePartition : CMP99SourceSquarePartition Q)
    (hpi5 : D.fineRegion (cmp99OmegaZeroIndex j) ⊆
      cmp99SourceTildePiLargeBlocks cell 5)
    (s : Fin (j + 2)) (hM : 2 ≤ M) (depth : ℕ)
    (center : FinBox 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)))
    {spacing epsilon : ℝ} (hspacing : 0 < spacing)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 M Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff 4 M (depth + 1)
      spacing epsilon < 1) :
    D.generatedPhysicalSmoothSectionCCommutatorFactorCoordinates fineProfile
        coarsePartition hpi5 s hM depth center hspacing background budget
          fineSmall hsmall =
      let Exterior := finitePiLpScalarMultiplier (g := SUNLieCoord Nc)
        (fun x : ActiveGaugeRegion.Site (D.operatorCoarseRegion hpi5 s) =>
          cmp99SourcePiCharacteristic cell x.1)
      let Middle :=
        D.generatedPhysicalSmoothSectionCCommutatorMiddleCoordinates
          fineProfile hpi5 s hM depth center hspacing background budget
            fineSmall hsmall
      let Head := D.generatedSectionCSourceHeadFactorCoordinates
        coarsePartition hpi5 s hM depth hspacing background budget fineSmall
          hsmall
      Exterior.comp (Middle.comp Head) := by
  rfl

/-- Fully source-generated specialization: one CMP95 profile produces both
the smooth fine cutoff and the periodic coarse head, and the complete
source-centred commutator ends in exactly that generated head. -/
theorem generatedCMP95SourceCenteredSectionCCommutatorFactorCoordinates_eq_head
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
      spacing epsilon < 1) :
    D.generatedCMP95SourceCenteredSectionCCommutatorFactorCoordinates P hpi5
        s hM depth hspacing background budget fineSmall hsmall =
      let Exterior := finitePiLpScalarMultiplier (g := SUNLieCoord Nc)
        (fun x : ActiveGaugeRegion.Site (D.operatorCoarseRegion hpi5 s) =>
          cmp99SourcePiCharacteristic cell x.1)
      let Middle :=
        D.generatedPhysicalSmoothSectionCCommutatorMiddleCoordinates P hpi5 s
          hM depth (cmp99SourceGeneratedSmoothCutoffCenter M Q depth cell)
            hspacing background budget fineSmall hsmall
      let Head := D.generatedCMP95SectionCSourceHeadFactorCoordinates P hpi5 s
        hM depth hspacing background budget fineSmall hsmall
      Exterior.comp (Middle.comp Head) := by
  rfl

end CMP99SourceDependentOmegaGeometry

end
end YangMills.RG
