/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceEq395AtomFactorization

/-!
# Bilateral support of the localized CMP99 equation (3.95) atoms

The second and third literal correction species have a leftmost `chi_Pi` or
`h_Pi`.  Together with their common rightmost `h_Pi`, this localizes both
kernel endpoints to the unique sixteen-block source cell.  The first species
is intentionally excluded: its global middle can propagate outside the cell
before the exterior factor `1 - chi_Pi` is applied.
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

namespace CMP99SourceDependentOmegaGeometry

set_option maxRecDepth 3000
set_option maxHeartbeats 750000

/-- The second atom vanishes at every target outside its literal source
base cell because its leftmost factor is `chi_Pi`. -/
theorem cmp99Eq395PhysicalRAtom_second_apply_single_eq_zero_of_target
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
    (cell : FinBox 4 Q) (source target : FinBox 4 (2 * Q))
    (v : SUNLieCoord Nc) (houtside : target ∉ cmp99SourceBaseCell cell) :
    cmp99Eq395PhysicalRAtom D hpi5 P hM depth hspacing background budget
      fineSmall hsmall (cell, .second) (singleFinitePiLp source v) target =
        0 := by
  have howner : cmp99SourceBaseCellOwner target ≠ cell := by
    intro heq
    exact houtside ((mem_cmp99SourceBaseCell_iff cell target).2 heq)
  simp [cmp99Eq395PhysicalRAtom, cmp99Eq395RAtom,
    cmp99Eq395SecondTerm, cmp99Eq395PhysicalSourceCharacteristic,
    finitePiLpScalarMultiplier_apply, cmp99SourcePiCharacteristic,
    cmp99SourceTildePiLargeBlocks_zero, howner]

/-- The third atom also vanishes outside the source base cell: its two
summands start respectively with `chi_Pi` and `h_Pi`. -/
theorem cmp99Eq395PhysicalRAtom_third_apply_single_eq_zero_of_target
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
    (cell : FinBox 4 Q) (source target : FinBox 4 (2 * Q))
    (v : SUNLieCoord Nc) (houtside : target ∉ cmp99SourceBaseCell cell) :
    cmp99Eq395PhysicalRAtom D hpi5 P hM depth hspacing background budget
      fineSmall hsmall (cell, .third) (singleFinitePiLp source v) target =
        0 := by
  have hnotSupport :
      ¬ cmp95SourcePeriodicCoarseCellSupport Q cell target := by
    intro hsupport
    exact houtside
      (cmp95SourcePeriodicCoarseCellSupport_mem_sourceBaseCell cell target
        hsupport)
  have hzero :
      (cmp95SourcePeriodicCoarseSquarePartition P Q).value cell target = 0 :=
    cmp95SourcePeriodicCoarseSquarePartition_value_eq_zero_of_not_support
      P Q cell target hnotSupport
  have howner : cmp99SourceBaseCellOwner target ≠ cell := by
    intro heq
    exact houtside ((mem_cmp99SourceBaseCell_iff cell target).2 heq)
  simp [cmp99Eq395PhysicalRAtom, cmp99Eq395RAtom,
    cmp99Eq395ThirdTerm, cmp99Eq395PhysicalSourceCharacteristic,
    cmp99Eq395PhysicalSmoothMultiplier, finitePiLpScalarMultiplier_apply,
    cmp99SourcePiCharacteristic, cmp99SourceTildePiLargeBlocks_zero,
    howner, hzero]

/-- Every non-first species has exact target support in the source base
cell. -/
theorem cmp99Eq395PhysicalRAtom_apply_single_eq_zero_of_target_of_ne_first
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
    (hspecies : species ≠ .first)
    (houtside : target ∉ cmp99SourceBaseCell cell) :
    cmp99Eq395PhysicalRAtom D hpi5 P hM depth hspacing background budget
      fineSmall hsmall (cell, species) (singleFinitePiLp source v) target =
        0 := by
  cases species with
  | first => exact (hspecies rfl).elim
  | second =>
      exact cmp99Eq395PhysicalRAtom_second_apply_single_eq_zero_of_target
        D hpi5 P hM depth hspacing background budget fineSmall hsmall cell
          source target v houtside
  | third =>
      exact cmp99Eq395PhysicalRAtom_third_apply_single_eq_zero_of_target
        D hpi5 P hM depth hspacing background budget fineSmall hsmall cell
          source target v houtside

/-- Bilateral exact base-cell support for every localized (non-first)
species. -/
theorem cmp99Eq395PhysicalRAtom_apply_single_eq_zero_of_endpoint_of_ne_first
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
    (hspecies : species ≠ .first)
    (houtside : source ∉ cmp99SourceBaseCell cell ∨
      target ∉ cmp99SourceBaseCell cell) :
    cmp99Eq395PhysicalRAtom D hpi5 P hM depth hspacing background budget
      fineSmall hsmall (cell, species) (singleFinitePiLp source v) target =
        0 := by
  rcases houtside with hsource | htarget
  · apply cmp99Eq395PhysicalRAtom_apply_single_eq_zero_of_source
    intro hsupport
    exact hsource
      (cmp95SourcePeriodicCoarseCellSupport_mem_sourceBaseCell cell source
        hsupport)
  · exact cmp99Eq395PhysicalRAtom_apply_single_eq_zero_of_target_of_ne_first
      D hpi5 P hM depth hspacing background budget fineSmall hsmall cell
        species source target v hspecies htarget

end CMP99SourceDependentOmegaGeometry

end
end YangMills.RG
