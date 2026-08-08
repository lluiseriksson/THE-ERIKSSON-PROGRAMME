/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceSectionCTypedFactorWalk
import YangMills.RG.BalabanCMP99SourceGeneratedSectionCSmoothCommutatorFactor
import YangMills.RG.BalabanCMP99SourceGeneratedSectionCCommutatorSupportWeightedRow

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

/-- Factorwise fixed-rate amplitude of the two reconstructed CMP99 Section C
species.  Rectangular cut steps and same-scale smooth commutators retain their
distinct source-derived constants. -/
noncomputable def generatedCMP95SectionCSourceLabelWeightedRowAmplitude
    (P : CMP95SourceSmoothPartitionProfile)
    (M depth : ℕ) (spacing epsilon rate : ℝ)
    {r s : Fin (j + 2)} :
    CMP99SectionCTypedFactorLabel j (fun _ _ => Empty) r s → ℝ
  | .cut _ =>
      cmp99SourceGeneratedPhysicalCoarseRightFactorWeightedRowAmplitude
        M depth spacing epsilon rate
  | .commutator _ =>
      cmp99SourceGeneratedCMP95SmoothCommutatorSupportWeightedRowAmplitude
        P M depth spacing epsilon rate
  | .other alpha => nomatch alpha

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

/-- Every reconstructed label has its source-derived fixed-rate weighted-row
certificate on the genuine cross-scale metric. -/
theorem generatedCMP95SectionCSourceLabelOperator_weightedRowKernelBound
    (D : CMP99SourceDependentOmegaGeometry
      (FinBox 4 (2 * Q)) j ScaleSite Scaled
      (cmp99SourceTildePiLargeBlocks cell 3)
      (cmp99SourceTildePiLargeBlocks cell 4) dist gap)
    (P : CMP95SourceSmoothPartitionProfile)
    (hpi5 : D.fineRegion (cmp99OmegaZeroIndex j) ⊆
      cmp99SourceTildePiLargeBlocks cell 5)
    (hM : 2 ≤ M) (depth : ℕ)
    {spacing epsilon rate : ℝ} (hspacing : 0 < spacing) (hrate : 0 < rate)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 M Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff 4 M (depth + 1)
      spacing epsilon < 1)
    {r s : Fin (j + 2)}
    (label : CMP99SectionCTypedFactorLabel j (fun _ _ => Empty) r s) :
    FinitePiLpTypedWeightedRowKernelBound
      (D.generatedCMP95SectionCSourceLabelOperator P hpi5 hM depth hspacing
        background budget fineSmall hsmall label)
      (D.generatedSectionCCoarseCrossDist hpi5 r s)
      (generatedCMP95SectionCSourceLabelWeightedRowAmplitude
        P M depth spacing epsilon rate label) rate := by
  cases label with
  | cut k =>
      simpa [generatedCMP95SectionCSourceLabelOperator,
        generatedCMP95SectionCSourceLabelWeightedRowAmplitude,
        generatedSectionCCutTowerStep,
        D.generatedSectionCCoarseCrossDist_transition hpi5 k] using
        D.generatedPhysicalCoarseSectionCCutFactorCoordinates_weightedRowKernelBound
          hpi5 k
          (D.generatedSectionCSourceTransitionCutData
            (cmp95SourcePeriodicCoarseSquarePartition P Q) hpi5 k)
          hM depth hspacing hrate background budget fineSmall hsmall
  | commutator _ =>
      simpa [generatedCMP95SectionCSourceLabelOperator,
        generatedCMP95SectionCSourceLabelWeightedRowAmplitude,
        generatedSectionCCoarseCrossDist,
        activeGaugeRegionSiteFinBoxDist] using
        D.generatedCMP95SourceCenteredSectionCCommutatorFactorCoordinates_weightedRow_supportSharp
          P hpi5 r hM depth hspacing hrate background budget fineSmall hsmall
  | other alpha => exact Empty.elim alpha

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

/-- Any well-typed walk over the reconstructed `cut` and `commutator`
species preserves one fixed spatial rate.  Its amplitude is the literal
ordered product of the two source-derived factor budgets selected by the
labels in the walk. -/
theorem generatedCMP95SectionCSourceOperatorWalk_weightedRowKernelBound
    (D : CMP99SourceDependentOmegaGeometry
      (FinBox 4 (2 * Q)) j ScaleSite Scaled
      (cmp99SourceTildePiLargeBlocks cell 3)
      (cmp99SourceTildePiLargeBlocks cell 4) dist gap)
    (P : CMP95SourceSmoothPartitionProfile)
    (hpi5 : D.fineRegion (cmp99OmegaZeroIndex j) ⊆
      cmp99SourceTildePiLargeBlocks cell 5)
    (hM : 2 ≤ M) (depth : ℕ)
    {spacing epsilon rate : ℝ} (hspacing : 0 < spacing) (hrate : 0 < rate)
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
      (CMP99SectionCTypedFactorLabel j (fun _ _ => Empty)) r s) :
    FinitePiLpTypedWeightedRowKernelBound
      (dependentFinitePiLpWalkOperator
        (D.GeneratedSectionCCoarseSiteFamily hpi5) (SUNLieCoord Nc)
        (D.generatedCMP95SectionCSourceOperatorWalk P hpi5 hM depth hspacing
          background budget fineSmall hsmall walk))
      (D.generatedSectionCCoarseCrossDist hpi5 r s)
      (walk.amplitude
        (generatedCMP95SectionCSourceLabelWeightedRowAmplitude
          P M depth spacing epsilon rate)) rate := by
  unfold generatedCMP95SectionCSourceOperatorWalk
  exact dependentFinitePiLpWalkOperator_map_weightedRowKernelBound
    (D.GeneratedSectionCCoarseSiteFamily hpi5) (SUNLieCoord Nc)
    (CMP99SectionCTypedFactorLabel j (fun _ _ => Empty))
    (D.generatedSectionCCoarseCrossDist hpi5)
    (fun q x => D.generatedSectionCCoarseCrossDist_self hpi5 q x)
    (fun q₀ q₁ q₂ target middle source =>
      D.generatedSectionCCoarseCrossDist_triangle hpi5 q₀ q₁ q₂ target
        middle source)
    (D.generatedCMP95SectionCSourceLabelOperator P hpi5 hM depth hspacing
      background budget fineSmall hsmall)
    (generatedCMP95SectionCSourceLabelWeightedRowAmplitude
      P M depth spacing epsilon rate)
    hrate.le
    (fun label =>
      D.generatedCMP95SectionCSourceLabelOperator_weightedRowKernelBound P
        hpi5 hM depth hspacing hrate background budget fineSmall hsmall label)
    walk

/-- Pointwise `(3.108)`-shaped consequence for every well-typed mixed walk
over the two reconstructed source species. -/
theorem generatedCMP95SectionCSourceOperatorWalk_exponentialKernelBound
    (D : CMP99SourceDependentOmegaGeometry
      (FinBox 4 (2 * Q)) j ScaleSite Scaled
      (cmp99SourceTildePiLargeBlocks cell 3)
      (cmp99SourceTildePiLargeBlocks cell 4) dist gap)
    (P : CMP95SourceSmoothPartitionProfile)
    (hpi5 : D.fineRegion (cmp99OmegaZeroIndex j) ⊆
      cmp99SourceTildePiLargeBlocks cell 5)
    (hM : 2 ≤ M) (depth : ℕ)
    {spacing epsilon rate : ℝ} (hspacing : 0 < spacing) (hrate : 0 < rate)
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
      (CMP99SectionCTypedFactorLabel j (fun _ _ => Empty)) r s) :
    FinitePiLpTypedExponentialKernelBound
      (dependentFinitePiLpWalkOperator
        (D.GeneratedSectionCCoarseSiteFamily hpi5) (SUNLieCoord Nc)
        (D.generatedCMP95SectionCSourceOperatorWalk P hpi5 hM depth hspacing
          background budget fineSmall hsmall walk))
      (D.generatedSectionCCoarseCrossDist hpi5 r s)
      (walk.amplitude
        (generatedCMP95SectionCSourceLabelWeightedRowAmplitude
          P M depth spacing epsilon rate)) rate :=
  finitePiLpTypedExponentialKernelBound_of_weightedRow _ _ hrate
    (D.generatedCMP95SectionCSourceOperatorWalk_weightedRowKernelBound P hpi5
      hM depth hspacing hrate background budget fineSmall hsmall walk)

/-- The canonical cut-only source label path interpreted from the CMP95
profile. -/
noncomputable def generatedCMP95SectionCSourceCutOperatorWalk
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
      spacing epsilon < 1) :=
  D.generatedCMP95SectionCSourceOperatorWalk P hpi5 hM depth hspacing
    background budget fineSmall hsmall (cmp99SectionCSourceCutLabelTower j)

/-- Exact identification of the profile-interpreted typed path with the
previously generated rectangular cut tower. -/
theorem generatedCMP95SectionCSourceCutOperatorWalk_eq_factorTower
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
      spacing epsilon < 1) :
    D.generatedCMP95SectionCSourceCutOperatorWalk P hpi5 hM depth hspacing
        background budget fineSmall hsmall =
      D.generatedSectionCSourceCutFactorTower
        (cmp95SourcePeriodicCoarseSquarePartition P Q) hpi5 hM depth hspacing
          background budget fineSmall hsmall := by
  unfold generatedCMP95SectionCSourceCutOperatorWalk
    generatedCMP95SectionCSourceOperatorWalk
    cmp99SectionCSourceCutLabelTower
    generatedSectionCSourceCutFactorTower
    generatedSectionCCutFactorTower
  simpa only [generatedCMP95SectionCSourceLabelOperator] using
    (DependentArrowWalk.map_finSuccPath
      (f := fun {r s}
        (label : CMP99SectionCTypedFactorLabel j
          (fun _ _ => Empty) r s) =>
        D.generatedCMP95SectionCSourceLabelOperator P hpi5 hM depth hspacing
          background budget fineSmall hsmall label)
      (step := fun r : Fin (j + 1) =>
        CMP99SectionCTypedFactorLabel.cut
          (Other := fun _ _ => Empty) r))

end CMP99SourceDependentOmegaGeometry

end

end YangMills.RG
