/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceGeneratedSectionCHeadSupportWeightedRow
import YangMills.RG.BalabanCMP99SourceSectionCSmoothTypedFactorWalk

/-!
# CMP99 Section C typed walks with the literal covariance head

CMP99 printed p. 413 specifies the head

`R'_0(Pi) = h_Pi C_Pi h_Pi`

before the generalized factors `R'_alpha(X)`.  This file conservatively
extends the already reconstructed `cut` and `commutator` alphabet by that
single head.  The old alphabet is embedded unchanged.  In particular, this
does not interpret the paper's non-exhaustive word "etc." as a complete
enumeration of all generalized species.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator RealInnerProductSpace

noncomputable section

universe v

/-- Conservative headed extension of the two-species coarse Section C
alphabet. -/
inductive CMP99SectionCHeadedTypedLabel (j : ℕ) :
    Fin (j + 2) → Fin (j + 2) → Type where
  | displayed {r s : Fin (j + 2)}
      (label : CMP99SectionCTypedFactorLabel j (fun _ _ => Empty) r s) :
      CMP99SectionCHeadedTypedLabel j r s
  | head (s : Fin (j + 2)) : CMP99SectionCHeadedTypedLabel j s s

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
set_option maxHeartbeats 1000000

/-- Factorwise fixed-rate amplitude for the old displayed species and the
literal covariance head. -/
noncomputable def generatedCMP95SectionCHeadedLabelWeightedRowAmplitude
    (P : CMP95SourceSmoothPartitionProfile)
    (M depth : ℕ) (spacing epsilon rate : ℝ)
    {r s : Fin (j + 2)} : CMP99SectionCHeadedTypedLabel j r s → ℝ
  | .displayed label =>
      generatedCMP95SectionCSourceLabelWeightedRowAmplitude
        P M depth spacing epsilon rate label
  | .head _ =>
      cmp99SourceGeneratedCMP95SectionCHeadWeightedRowAmplitude
        M depth spacing epsilon rate

/-- Source interpretation of the headed alphabet.  The head uses the exact
periodic square partition generated from CMP95 (1.118). -/
noncomputable def generatedCMP95SectionCHeadedLabelOperator
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
    {r s : Fin (j + 2)} : CMP99SectionCHeadedTypedLabel j r s →
      DependentFinitePiLpArrow (D.GeneratedSectionCCoarseSiteFamily hpi5)
        (SUNLieCoord Nc) r s := by
  intro label
  cases label with
  | displayed old =>
      exact D.generatedCMP95SectionCSourceLabelOperator P hpi5 hM depth
        hspacing background budget fineSmall hsmall old
  | head =>
      exact D.generatedCMP95SectionCSourceHeadFactorCoordinates P hpi5 r hM
        depth hspacing background budget fineSmall hsmall

@[simp] theorem generatedCMP95SectionCHeadedLabelOperator_displayed
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
    (label : CMP99SectionCTypedFactorLabel j (fun _ _ => Empty) r s) :
    D.generatedCMP95SectionCHeadedLabelOperator P hpi5 hM depth hspacing
        background budget fineSmall hsmall
        (CMP99SectionCHeadedTypedLabel.displayed label) =
      D.generatedCMP95SectionCSourceLabelOperator P hpi5 hM depth hspacing
        background budget fineSmall hsmall label := by
  simp [generatedCMP95SectionCHeadedLabelOperator]

@[simp] theorem generatedCMP95SectionCHeadedLabelOperator_head
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
    D.generatedCMP95SectionCHeadedLabelOperator P hpi5 hM depth hspacing
        background budget fineSmall hsmall
        (CMP99SectionCHeadedTypedLabel.head s) =
      D.generatedCMP95SectionCSourceHeadFactorCoordinates P hpi5 s hM depth
        hspacing background budget fineSmall hsmall := by
  simp [generatedCMP95SectionCHeadedLabelOperator]

/-- Every label in the conservative headed alphabet has its source-derived
fixed-rate weighted row. -/
theorem generatedCMP95SectionCHeadedLabelOperator_weightedRow
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
    {r s : Fin (j + 2)} (label : CMP99SectionCHeadedTypedLabel j r s) :
    FinitePiLpTypedWeightedRowKernelBound
      (D.generatedCMP95SectionCHeadedLabelOperator P hpi5 hM depth hspacing
        background budget fineSmall hsmall label)
      (D.generatedSectionCCoarseCrossDist hpi5 r s)
      (generatedCMP95SectionCHeadedLabelWeightedRowAmplitude
        P M depth spacing epsilon rate label) rate := by
  cases label with
  | displayed old =>
      simpa [generatedCMP95SectionCHeadedLabelOperator,
        generatedCMP95SectionCHeadedLabelWeightedRowAmplitude] using
        D.generatedCMP95SectionCSourceLabelOperator_weightedRowKernelBound
          P hpi5 hM depth hspacing hrate background budget fineSmall hsmall old
  | head =>
      simpa [generatedCMP95SectionCHeadedLabelOperator,
        generatedCMP95SectionCHeadedLabelWeightedRowAmplitude,
        generatedSectionCSourceHeadFactorCertificate,
        generatedSectionCCoarseCrossDist,
        activeGaugeRegionSiteFinBoxDist] using
        D.generatedCMP95SectionCSourceHeadFactorCoordinates_weightedRow_supportSharp P
          hpi5 r hM depth hspacing hrate background budget fineSmall hsmall

/-- Any well-typed word over the displayed coarse species and the literal
head preserves one spatial rate. -/
theorem generatedCMP95SectionCHeadedOperatorWalk_weightedRow
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
    (walk : DependentArrowWalk (CMP99SectionCHeadedTypedLabel j) r s) :
    FinitePiLpTypedWeightedRowKernelBound
      (dependentFinitePiLpWalkOperator
        (D.GeneratedSectionCCoarseSiteFamily hpi5) (SUNLieCoord Nc)
        (walk.map (D.generatedCMP95SectionCHeadedLabelOperator P hpi5 hM
          depth hspacing background budget fineSmall hsmall)))
      (D.generatedSectionCCoarseCrossDist hpi5 r s)
      (walk.amplitude (generatedCMP95SectionCHeadedLabelWeightedRowAmplitude
        P M depth spacing epsilon rate)) rate := by
  exact dependentFinitePiLpWalkOperator_map_weightedRowKernelBound
    (D.GeneratedSectionCCoarseSiteFamily hpi5) (SUNLieCoord Nc)
    (CMP99SectionCHeadedTypedLabel j)
    (D.generatedSectionCCoarseCrossDist hpi5)
    (fun q x => D.generatedSectionCCoarseCrossDist_self hpi5 q x)
    (fun q₀ q₁ q₂ target middle source =>
      D.generatedSectionCCoarseCrossDist_triangle hpi5 q₀ q₁ q₂ target
        middle source)
    (D.generatedCMP95SectionCHeadedLabelOperator P hpi5 hM depth hspacing
      background budget fineSmall hsmall)
    (generatedCMP95SectionCHeadedLabelWeightedRowAmplitude
      P M depth spacing epsilon rate)
    hrate.le
    (fun label => D.generatedCMP95SectionCHeadedLabelOperator_weightedRow P
      hpi5 hM depth hspacing hrate background budget fineSmall hsmall label)
    walk

/-- Pointwise `(3.108)`-shaped consequence for every headed coarse word. -/
theorem generatedCMP95SectionCHeadedOperatorWalk_exponential
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
    (walk : DependentArrowWalk (CMP99SectionCHeadedTypedLabel j) r s) :
    FinitePiLpTypedExponentialKernelBound
      (dependentFinitePiLpWalkOperator
        (D.GeneratedSectionCCoarseSiteFamily hpi5) (SUNLieCoord Nc)
        (walk.map (D.generatedCMP95SectionCHeadedLabelOperator P hpi5 hM
          depth hspacing background budget fineSmall hsmall)))
      (D.generatedSectionCCoarseCrossDist hpi5 r s)
      (walk.amplitude (generatedCMP95SectionCHeadedLabelWeightedRowAmplitude
        P M depth spacing epsilon rate)) rate :=
  finitePiLpTypedExponentialKernelBound_of_weightedRow _ _ hrate
    (D.generatedCMP95SectionCHeadedOperatorWalk_weightedRow P hpi5 hM depth
      hspacing hrate background budget fineSmall hsmall walk)

end CMP99SourceDependentOmegaGeometry

end
end YangMills.RG
