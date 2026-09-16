/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceEq395CorrectionSharpWeightedRow
import YangMills.RG.FinitePiLpScalarCommutator

/-!
# Cellwise cancellation in the CMP99 equation (3.95) correction

The three printed species should not be estimated independently once their
common source cell is fixed.  Their signed sum is the local parametrix error.
This file exposes that cancellation in the literal physical operators and
shows that a point source sees exactly the grouped operator of its unique
base-cell owner.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped BigOperators Matrix.Norms.L2Operator RealInnerProductSpace

noncomputable section

universe u v

/-- The signed three-species correction attached to one index. -/
def cmp99Eq395GroupedRAtom {Index : Type u} {E : Type v} [Ring E]
    (A : E) (AD chi h C : Index → E) (i : Index) : E :=
  ∑ species : CMP99Eq395CorrectionSpecies,
    cmp99Eq395RAtom A AD chi h C (i, species)

/-- Exact cellwise cancellation before any norm is applied. -/
theorem cmp99Eq395GroupedRAtom_eq
    {Index : Type u} {E : Type v} [Ring E]
    (A : E) (AD chi h C : Index → E) (i : Index) :
    cmp99Eq395GroupedRAtom A AD chi h C i =
      h i * (chi i * AD i) * C i * h i - A * (h i * C i * h i) := by
  unfold cmp99Eq395GroupedRAtom
  rw [show (Finset.univ : Finset CMP99Eq395CorrectionSpecies) =
      {.first, .second, .third} by
    ext species
    cases species <;> simp]
  simp only [Finset.sum_insert, Finset.mem_insert,
    Finset.mem_singleton, reduceCtorEq, or_self, not_false_eq_true,
    Finset.sum_singleton, cmp99Eq395RAtom]
  calc
    -cmp99Eq395FirstTerm A (chi i) (h i) (C i) +
          (-cmp99Eq395SecondTerm A (AD i) (chi i) (h i) (C i) +
            -cmp99Eq395ThirdTerm (AD i) (chi i) (h i) (C i)) =
        -(cmp99Eq395FirstTerm A (chi i) (h i) (C i) +
          cmp99Eq395SecondTerm A (AD i) (chi i) (h i) (C i) +
          cmp99Eq395ThirdTerm (AD i) (chi i) (h i) (C i)) := by abel
    _ = h i * (chi i * AD i) * C i * h i -
          A * (h i * C i * h i) := by
      rw [cmp99Eq395_threeTerms_eq]
      noncomm_ring

variable {M Nc Q j : ℕ} [NeZero M] [NeZero Nc] [NeZero Q]
variable {ScaleSite : Fin (j + 2) → Type v}
variable [∀ r, DecidableEq (ScaleSite r)]
variable {Scaled : CMP99SourceScaledStratification
  (FinBox 4 (2 * Q)) (j + 2) ScaleSite}
variable {dist : FinBox 4 (2 * Q) → FinBox 4 (2 * Q) → ℕ}
variable {gap : Fin (j + 1) → ℕ}

namespace CMP99SourceDependentOmegaGeometry

/-- Literal grouped physical correction of one source cell. -/
noncomputable def cmp99Eq395PhysicalGroupedRAtom
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
    (cell : FinBox 4 Q) : CMP99Eq395AmbientOperator Q Nc :=
  ∑ species : CMP99Eq395CorrectionSpecies,
    cmp99Eq395PhysicalRAtom D hpi5 P hM depth hspacing background budget
      fineSmall hsmall (cell, species)

/-- The single gluing defect left after the three printed species are
combined.  This is the source-faithful analytic target: global propagation
through the smooth cutoff minus the cutoff transport of the regional
precision. -/
noncomputable def cmp99Eq395PhysicalGroupedLeftDefect
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
    (cell : FinBox 4 Q) : CMP99Eq395AmbientOperator Q Nc :=
  let A := cmp99Eq395PhysicalGlobalMiddle hM depth hspacing background
    budget fineSmall hsmall
  let h := cmp99Eq395PhysicalSmoothMultiplier (Nc := Nc) P cell
  let chi := cmp99Eq395PhysicalSourceCharacteristic (Nc := Nc) cell
  let AD := cmp99Eq395PhysicalMiddle D hpi5 hM depth hspacing background
    budget fineSmall hsmall cell
  A * h - h * (chi * AD)

/-- The third source mechanism is literally the scalar-multiplier
commutator `[chi_Pi A_Pi, h_Pi]`.  This is an exact dictionary theorem;
the cutoff-slope estimate is deliberately left to the analytic layer. -/
theorem cmp99Eq395PhysicalThirdLeft_eq_operatorScalarCommutator
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
    (cell : FinBox 4 Q) :
    cmp99Eq395PhysicalThirdLeft D hpi5 P hM depth hspacing background
        budget fineSmall hsmall cell =
      finitePiLpOperatorScalarCommutator
        (cmp99Eq395PhysicalSourceCharacteristic (Nc := Nc) cell *
          cmp99Eq395PhysicalMiddle D hpi5 hM depth hspacing background
            budget fineSmall hsmall cell)
        (fun block : FinBox 4 (2 * Q) =>
          (cmp95SourcePeriodicCoarseSquarePartition P Q).value cell block) := by
  rfl

/-- Exact source decomposition of the grouped gluing defect.  The three
summands are precisely the exterior propagation, global--regional mismatch,
and smooth-cutoff commutator printed in (3.95); no estimate is inserted. -/
theorem cmp99Eq395PhysicalGroupedLeftDefect_eq_three_source_mechanisms
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
    (cell : FinBox 4 Q) :
    cmp99Eq395PhysicalGroupedLeftDefect D hpi5 P hM depth hspacing
        background budget fineSmall hsmall cell =
      cmp99Eq395PhysicalFirstLeft hM depth hspacing background budget
          fineSmall hsmall cell *
        cmp99Eq395PhysicalSmoothMultiplier (Nc := Nc) P cell +
      cmp99Eq395PhysicalSecondLeft D hpi5 hM depth hspacing background budget
          fineSmall hsmall cell *
        cmp99Eq395PhysicalSmoothMultiplier (Nc := Nc) P cell +
      cmp99Eq395PhysicalThirdLeft D hpi5 P hM depth hspacing background
        budget fineSmall hsmall cell := by
  unfold cmp99Eq395PhysicalGroupedLeftDefect
    cmp99Eq395PhysicalFirstLeft cmp99Eq395PhysicalSecondLeft
    cmp99Eq395PhysicalThirdLeft
  dsimp only
  simp only [sub_mul, mul_sub, one_mul, mul_assoc]
  module

set_option maxRecDepth 4000
set_option maxHeartbeats 4000000

/-- The physical grouped atom is `h_Pi^2 - A h_Pi C_Pi h_Pi`.  The regional
middle and covariance have disappeared through their exact projected inverse
identity; this is the cancellation lost by separate atom norms. -/
theorem cmp99Eq395PhysicalGroupedRAtom_eq_square_sub_global_head
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
    (cell : FinBox 4 Q) :
    let h := cmp99Eq395PhysicalSmoothMultiplier (Nc := Nc) P cell
    let A := cmp99Eq395PhysicalGlobalMiddle hM depth hspacing background
      budget fineSmall hsmall
    let C := cmp99Eq395PhysicalCovariance D hpi5 hM depth hspacing background
      budget fineSmall hsmall cell
    cmp99Eq395PhysicalGroupedRAtom D hpi5 P hM depth hspacing background
        budget fineSmall hsmall cell =
      h * h - A * (h * C * h) := by
  dsimp only
  let A := cmp99Eq395PhysicalGlobalMiddle hM depth hspacing background budget
    fineSmall hsmall
  let AD := cmp99Eq395PhysicalMiddle D hpi5 hM depth hspacing background
    budget fineSmall hsmall cell
  let chi := cmp99Eq395PhysicalSourceCharacteristic (Nc := Nc) cell
  let proj := cmp99Eq395PhysicalRegionProjector (Nc := Nc) D hpi5 cell
  let h := cmp99Eq395PhysicalSmoothMultiplier (Nc := Nc) P cell
  let C := cmp99Eq395PhysicalCovariance D hpi5 hM depth hspacing background
    budget fineSmall hsmall cell
  have hsupport : h * chi = h := by
    simpa [h, chi, cmp99Eq395PhysicalSmoothMultiplier,
      cmp99Eq395PhysicalSourceCharacteristic] using
      (cmp95SourcePeriodicCoarseSquarePartition_multiplier_comp_characteristic
        (g := SUNLieCoord Nc) P cell (fun block => block))
  have hregion : h * proj = h := by
    simpa [h, proj, cmp99Eq395PhysicalSmoothMultiplier,
      cmp99Eq395PhysicalRegionProjector] using
      ((D cell).cmp95SourcePeriodicCoarseSquarePartition_multiplier_comp_pi4RegionProjector
        (hpi5 cell) (Nc := Nc) P)
  have hinverse : AD * C = proj := by
    simpa [AD, C, proj, cmp99Eq395PhysicalMiddle,
      cmp99Eq395PhysicalCovariance, cmp99Eq395PhysicalRegionProjector] using
      ((D cell).generatedPhysicalCoarseCovarianceMiddleAmbient_comp_covarianceAmbient
        (hpi5 cell) (cmp99OmegaPi4Index j) hM depth hspacing background
        budget fineSmall hsmall)
  have hresolution : h * (chi * AD) * C * h = h * h :=
    cmp99Eq395_local_resolution_term_of_projected_inverse AD chi proj h C
      hsupport hregion hinverse
  rw [show cmp99Eq395PhysicalGroupedRAtom D hpi5 P hM depth hspacing
      background budget fineSmall hsmall cell =
      cmp99Eq395GroupedRAtom A
        (cmp99Eq395PhysicalMiddle D hpi5 hM depth hspacing background budget
          fineSmall hsmall)
        (cmp99Eq395PhysicalSourceCharacteristic (Nc := Nc))
        (cmp99Eq395PhysicalSmoothMultiplier (Nc := Nc) P)
        (cmp99Eq395PhysicalCovariance D hpi5 hM depth hspacing background
          budget fineSmall hsmall) cell by rfl]
  rw [cmp99Eq395GroupedRAtom_eq, hresolution]

/-- Final source-faithful factorization of the grouped cell error.  All three
printed correction species are represented by one gluing defect followed by
the literal regional covariance tail. -/
theorem cmp99Eq395PhysicalGroupedRAtom_eq_neg_defect_comp_tail
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
    (cell : FinBox 4 Q) :
    cmp99Eq395PhysicalGroupedRAtom D hpi5 P hM depth hspacing background
        budget fineSmall hsmall cell =
      -(cmp99Eq395PhysicalGroupedLeftDefect D hpi5 P hM depth hspacing
          background budget fineSmall hsmall cell) *
        cmp99Eq395PhysicalCovariance D hpi5 hM depth hspacing background
          budget fineSmall hsmall cell *
        cmp99Eq395PhysicalSmoothMultiplier (Nc := Nc) P cell := by
  let A := cmp99Eq395PhysicalGlobalMiddle hM depth hspacing background budget
    fineSmall hsmall
  let AD := cmp99Eq395PhysicalMiddle D hpi5 hM depth hspacing background
    budget fineSmall hsmall cell
  let chi := cmp99Eq395PhysicalSourceCharacteristic (Nc := Nc) cell
  let proj := cmp99Eq395PhysicalRegionProjector (Nc := Nc) D hpi5 cell
  let h := cmp99Eq395PhysicalSmoothMultiplier (Nc := Nc) P cell
  let C := cmp99Eq395PhysicalCovariance D hpi5 hM depth hspacing background
    budget fineSmall hsmall cell
  have hsupport : h * chi = h := by
    simpa [h, chi, cmp99Eq395PhysicalSmoothMultiplier,
      cmp99Eq395PhysicalSourceCharacteristic] using
      (cmp95SourcePeriodicCoarseSquarePartition_multiplier_comp_characteristic
        (g := SUNLieCoord Nc) P cell (fun block => block))
  have hregion : h * proj = h := by
    simpa [h, proj, cmp99Eq395PhysicalSmoothMultiplier,
      cmp99Eq395PhysicalRegionProjector] using
      ((D cell).cmp95SourcePeriodicCoarseSquarePartition_multiplier_comp_pi4RegionProjector
        (hpi5 cell) (Nc := Nc) P)
  have hinverse : AD * C = proj := by
    simpa [AD, C, proj, cmp99Eq395PhysicalMiddle,
      cmp99Eq395PhysicalCovariance, cmp99Eq395PhysicalRegionProjector] using
      ((D cell).generatedPhysicalCoarseCovarianceMiddleAmbient_comp_covarianceAmbient
        (hpi5 cell) (cmp99OmegaPi4Index j) hM depth hspacing background
        budget fineSmall hsmall)
  rw [cmp99Eq395PhysicalGroupedRAtom_eq_square_sub_global_head D hpi5 P hM
    depth hspacing background budget fineSmall hsmall cell]
  change h * h - A * (h * C * h) = -(A * h - h * (chi * AD)) * C * h
  calc
    h * h - A * (h * C * h) =
        h * (chi * AD) * C * h - A * (h * C * h) := by
      rw [cmp99Eq395_local_resolution_term_of_projected_inverse AD chi proj h C
        hsupport hregion hinverse]
    _ = -(A * h - h * (chi * AD)) * C * h := by
      rw [neg_sub]
      noncomm_ring
      rw [← mul_assoc A h (C * h), smul_mul_assoc]

/-- On a point source the complete correction is exactly the grouped atom
of the unique source-cell owner.  No estimate or source branching remains in
this identity. -/
theorem cmp99Eq395PhysicalCorrection_apply_single_eq_grouped_owner
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
      cmp99Eq395PhysicalGroupedRAtom D hpi5 P hM depth hspacing background
        budget fineSmall hsmall (cmp99SourceBaseCellOwner source)
          (singleFinitePiLp source v) target := by
  classical
  let relevant := cmp99Eq395SourceRelevantLabels source
  let owner := cmp99SourceBaseCellOwner source
  let ownerFiber : Finset (FinBox 4 Q × CMP99Eq395CorrectionSpecies) :=
    {owner} ×ˢ Finset.univ
  have hsubset : relevant ⊆ ownerFiber := by
    intro label hlabel
    rw [Finset.mem_product]
    exact ⟨by
      simpa [relevant, owner] using
        fst_eq_sourceBaseCellOwner_of_mem_cmp99Eq395SourceRelevantLabels
          source label hlabel, Finset.mem_univ _⟩
  rw [cmp99Eq395PhysicalCorrection_apply_single_eq_sum_relevant D hpi5 P hM
    depth hspacing background budget fineSmall hsmall]
  change (∑ label ∈ relevant,
      cmp99Eq395PhysicalRAtom D hpi5 P hM depth hspacing background budget
        fineSmall hsmall label (singleFinitePiLp source v) target) = _
  have hsum : (∑ label ∈ relevant,
      cmp99Eq395PhysicalRAtom D hpi5 P hM depth hspacing background budget
        fineSmall hsmall label (singleFinitePiLp source v) target) =
      ∑ label ∈ ownerFiber,
        cmp99Eq395PhysicalRAtom D hpi5 P hM depth hspacing background budget
          fineSmall hsmall label (singleFinitePiLp source v) target := by
    apply Finset.sum_subset hsubset
    intro label howner hnot
    have houtside :
        ¬ cmp95SourcePeriodicCoarseCellSupport Q label.1 source := by
      simpa [relevant, mem_cmp99Eq395SourceRelevantLabels_iff] using hnot
    exact cmp99Eq395PhysicalRAtom_apply_single_eq_zero_of_source D hpi5 P hM
      depth hspacing background budget fineSmall hsmall label.1 label.2 source
        target v houtside
  rw [hsum]
  simp [ownerFiber, owner, cmp99Eq395PhysicalGroupedRAtom]

end CMP99SourceDependentOmegaGeometry
end
end YangMills.RG
