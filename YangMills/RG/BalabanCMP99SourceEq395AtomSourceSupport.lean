/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceEq395WalkExpansion
import YangMills.RG.BalabanCMP99SourceEq395HeadSupport

/-!
# Source support of the exhaustive CMP99 equation (3.95) atoms

Every one of the three literal correction species ends with the same smooth
source multiplier `h_Pi`.  Hence a point source can activate atoms from only
its unique CMP99 base cell.  This reduces the source branching of the exact
three-species alphabet from `3 * |Lambda|` to at most three, before any
analytic estimate is used.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped BigOperators Matrix.Norms.L2Operator RealInnerProductSpace

noncomputable section

universe v

variable {M Nc Q j : ℕ} [NeZero M] [NeZero Nc] [NeZero Q]
variable {ScaleSite : Fin (j + 2) → Type v}
variable [∀ r, DecidableEq (ScaleSite r)]
variable {Scaled : CMP99SourceScaledStratification
  (FinBox 4 (2 * Q)) (j + 2) ScaleSite}
variable {dist : FinBox 4 (2 * Q) → FinBox 4 (2 * Q) → ℕ}
variable {gap : Fin (j + 1) → ℕ}

/-- Exact alphabet labels whose source cutoff can be nonzero at a given
ambient coarse block. -/
noncomputable def cmp99Eq395SourceRelevantLabels
    (source : FinBox 4 (2 * Q)) :
    Finset (FinBox 4 Q × CMP99Eq395CorrectionSpecies) := by
  classical
  exact Finset.univ.filter fun label =>
    cmp95SourcePeriodicCoarseCellSupport Q label.1 source

@[simp] theorem mem_cmp99Eq395SourceRelevantLabels_iff
    (source : FinBox 4 (2 * Q))
    (label : FinBox 4 Q × CMP99Eq395CorrectionSpecies) :
    label ∈ cmp99Eq395SourceRelevantLabels source ↔
      cmp95SourcePeriodicCoarseCellSupport Q label.1 source := by
  classical
  simp [cmp99Eq395SourceRelevantLabels]

/-- Every relevant label has the unique base-cell owner of the source as its
geometric component. -/
theorem fst_eq_sourceBaseCellOwner_of_mem_cmp99Eq395SourceRelevantLabels
    (source : FinBox 4 (2 * Q))
    (label : FinBox 4 Q × CMP99Eq395CorrectionSpecies)
    (hlabel : label ∈ cmp99Eq395SourceRelevantLabels source) :
    label.1 = cmp99SourceBaseCellOwner source := by
  have hsupport : cmp95SourcePeriodicCoarseCellSupport Q label.1 source :=
    (mem_cmp99Eq395SourceRelevantLabels_iff source label).mp hlabel
  have hcell :=
    cmp95SourcePeriodicCoarseCellSupport_mem_sourceBaseCell label.1 source
      hsupport
  rw [mem_cmp99SourceBaseCell_iff] at hcell
  exact hcell.symm

/-- Volume-independent source branching: no more than the three literal
species can act on a fixed point source. -/
theorem card_cmp99Eq395SourceRelevantLabels_le_three
    (source : FinBox 4 (2 * Q)) :
    (cmp99Eq395SourceRelevantLabels source).card ≤ 3 := by
  classical
  let ownerFiber : Finset (FinBox 4 Q × CMP99Eq395CorrectionSpecies) :=
    {cmp99SourceBaseCellOwner source} ×ˢ Finset.univ
  have hsubset : cmp99Eq395SourceRelevantLabels source ⊆ ownerFiber := by
    intro label hlabel
    rw [Finset.mem_product]
    exact ⟨by
      simpa using
        fst_eq_sourceBaseCellOwner_of_mem_cmp99Eq395SourceRelevantLabels
          source label hlabel, Finset.mem_univ _⟩
  calc
    (cmp99Eq395SourceRelevantLabels source).card ≤ ownerFiber.card :=
      Finset.card_le_card hsubset
    _ = 3 := by
      simp [ownerFiber]
      rfl

namespace CMP99SourceDependentOmegaGeometry

set_option maxRecDepth 3000
set_option maxHeartbeats 750000

/-- Every literal correction atom annihilates a point source outside its
own CMP95 source cell. -/
theorem cmp99Eq395PhysicalRAtom_apply_single_eq_zero_of_source
    (D : (cell : FinBox 4 Q) → CMP99SourceDependentOmegaGeometry
      (FinBox 4 (2 * Q)) j ScaleSite Scaled
      (cmp99SourceTildePiLargeBlocks cell 3)
      (cmp99SourceTildePiLargeBlocks cell 4) dist gap)
    (hpi5 : ∀ cell, (D cell).fineRegion (cmp99OmegaZeroIndex j) ⊆
      cmp99SourceTildePiLargeBlocks cell 5)
    (P : CMP95SourceSmoothPartitionProfile)
    (hM : 2 ≤ M) (depth : ℕ) {spacing epsilon : ℝ}
    (hspacing : 0 < spacing)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 M Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff 4 M (depth + 1)
      spacing epsilon < 1)
    (cell : FinBox 4 Q) (species : CMP99Eq395CorrectionSpecies)
    (source target : FinBox 4 (2 * Q)) (v : SUNLieCoord Nc)
    (houtside : ¬ cmp95SourcePeriodicCoarseCellSupport Q cell source) :
    cmp99Eq395PhysicalRAtom D hpi5 P hM depth hspacing background budget
      fineSmall hsmall (cell, species) (singleFinitePiLp source v) target = 0 := by
  have hzero :
      (cmp95SourcePeriodicCoarseSquarePartition P Q).value cell source = 0 :=
    cmp95SourcePeriodicCoarseSquarePartition_value_eq_zero_of_not_support
      P Q cell source houtside
  have hsingle : singleFinitePiLp source (0 : SUNLieCoord Nc) = 0 := by
    apply PiLp.ext
    intro x
    by_cases hx : x = source
    · subst x
      simp
    · rw [singleFinitePiLp_of_ne (0 : SUNLieCoord Nc) hx]
      rfl
  cases species <;>
    simp [cmp99Eq395PhysicalRAtom, cmp99Eq395RAtom,
      cmp99Eq395FirstTerm, cmp99Eq395SecondTerm, cmp99Eq395ThirdTerm,
      cmp99Eq395PhysicalSmoothMultiplier, finitePiLpScalarMultiplier_single,
      hzero, hsingle]

/-- On a one-site input the complete finite atom sum reduces exactly to the
at-most-three relevant labels. -/
theorem sum_cmp99Eq395PhysicalRAtom_apply_single_eq_sum_relevant
    (D : (cell : FinBox 4 Q) → CMP99SourceDependentOmegaGeometry
      (FinBox 4 (2 * Q)) j ScaleSite Scaled
      (cmp99SourceTildePiLargeBlocks cell 3)
      (cmp99SourceTildePiLargeBlocks cell 4) dist gap)
    (hpi5 : ∀ cell, (D cell).fineRegion (cmp99OmegaZeroIndex j) ⊆
      cmp99SourceTildePiLargeBlocks cell 5)
    (P : CMP95SourceSmoothPartitionProfile)
    (hM : 2 ≤ M) (depth : ℕ) {spacing epsilon : ℝ}
    (hspacing : 0 < spacing)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 M Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff 4 M (depth + 1)
      spacing epsilon < 1)
    (source target : FinBox 4 (2 * Q)) (v : SUNLieCoord Nc) :
    (∑ label : FinBox 4 Q × CMP99Eq395CorrectionSpecies,
        cmp99Eq395PhysicalRAtom D hpi5 P hM depth hspacing background budget
          fineSmall hsmall label) (singleFinitePiLp source v) target =
      ∑ label ∈ cmp99Eq395SourceRelevantLabels source,
        cmp99Eq395PhysicalRAtom D hpi5 P hM depth hspacing background budget
          fineSmall hsmall label (singleFinitePiLp source v) target := by
  classical
  simp only [ContinuousLinearMap.sum_apply]
  rw [WithLp.ofLp_sum, Finset.sum_apply]
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro label _ hlabel
  have houtside :
      ¬ cmp95SourcePeriodicCoarseCellSupport Q label.1 source := by
    simpa [mem_cmp99Eq395SourceRelevantLabels_iff] using hlabel
  exact cmp99Eq395PhysicalRAtom_apply_single_eq_zero_of_source D hpi5 P hM
    depth hspacing background budget fineSmall hsmall label.1 label.2 source
      target v houtside

/-- The exact correction itself therefore has a point-source expansion with
at most three active summands, uniformly in the ambient volume. -/
theorem cmp99Eq395PhysicalCorrection_apply_single_eq_sum_relevant
    (D : (cell : FinBox 4 Q) → CMP99SourceDependentOmegaGeometry
      (FinBox 4 (2 * Q)) j ScaleSite Scaled
      (cmp99SourceTildePiLargeBlocks cell 3)
      (cmp99SourceTildePiLargeBlocks cell 4) dist gap)
    (hpi5 : ∀ cell, (D cell).fineRegion (cmp99OmegaZeroIndex j) ⊆
      cmp99SourceTildePiLargeBlocks cell 5)
    (P : CMP95SourceSmoothPartitionProfile)
    (hM : 2 ≤ M) (depth : ℕ) {spacing epsilon : ℝ}
    (hspacing : 0 < spacing)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 M Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff 4 M (depth + 1)
      spacing epsilon < 1)
    (source target : FinBox 4 (2 * Q)) (v : SUNLieCoord Nc) :
    cmp99Eq395PhysicalCorrection D hpi5 P hM depth hspacing background budget
        fineSmall hsmall (singleFinitePiLp source v) target =
      ∑ label ∈ cmp99Eq395SourceRelevantLabels source,
        cmp99Eq395PhysicalRAtom D hpi5 P hM depth hspacing background budget
          fineSmall hsmall label (singleFinitePiLp source v) target := by
  rw [← sum_cmp99Eq395PhysicalRAtom_eq_correction]
  exact sum_cmp99Eq395PhysicalRAtom_apply_single_eq_sum_relevant D hpi5 P hM
    depth hspacing background budget fineSmall hsmall source target v

end CMP99SourceDependentOmegaGeometry

end
end YangMills.RG
