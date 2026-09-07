/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceGeneratedSectionCSmoothBasicAdjointDecay
import YangMills.RG.BalabanCMP99SourceSectionCSmoothHeterogeneousFactorWalk

/-!
# Fixed-rate decay for the heterogeneous CMP99 Section C walk

CMP99 printed pp. 412--413 composes the fine-space factor
`K(h'_Pi)G'_Pi h'_Pi` with its rectangular extension
`K(h'_Pi)G'_Pi h'_Pi Q'^*`.  The latter starts on the terminal coarse field,
so its spatial kernel becomes visible only after the proved equality between
the generated terminal Hilbert bundle and its physical coordinate bundle.

This module uses that coordinate bundle as the site family of a dependent
walk.  Both displayed species then carry fixed-rate weighted rows, and every
well-typed heterogeneous word inherits their ordered product without an
ambient-volume factor or loss of the spatial rate.

Honest scope: CMP99's printed word "etc." remains non-exhaustive.  Only the
two displayed basic species are interpreted here.
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

/-- The physical coordinate type carried by a heterogeneous Section C
index.  The coarse member is the exposed terminal coordinate type; the fine
member is the genuine lifted regional site type. -/
noncomputable def generatedSectionCHeterogeneousCoordinateSite
    (D : CMP99SourceDependentOmegaGeometry
      (FinBox 4 (2 * Q)) j ScaleSite Scaled
      (cmp99SourceTildePiLargeBlocks cell 3)
      (cmp99SourceTildePiLargeBlocks cell 4) dist gap)
    (hpi5 : D.fineRegion (cmp99OmegaZeroIndex j) ⊆
      cmp99SourceTildePiLargeBlocks cell 5)
    (M depth : ℕ) [NeZero M]
    (i : CMP99SectionCHeterogeneousIndex j) : Type := by
  let Omega := D.operatorCoarseRegion hpi5 i.1
  let regions := cmp99SourceIteratedLiftActiveRegionChain
    (M := M) Omega (depth + 1)
  exact match i.2 with
    | .coarse => regions.terminalSite
    | .fine => ActiveGaugeRegion.Site
        (cmp99IteratedLiftActiveRegion (M := M) Omega (depth + 1))

noncomputable instance generatedSectionCHeterogeneousCoordinateSiteFintype
    (D : CMP99SourceDependentOmegaGeometry
      (FinBox 4 (2 * Q)) j ScaleSite Scaled
      (cmp99SourceTildePiLargeBlocks cell 3)
      (cmp99SourceTildePiLargeBlocks cell 4) dist gap)
    (hpi5 : D.fineRegion (cmp99OmegaZeroIndex j) ⊆
      cmp99SourceTildePiLargeBlocks cell 5)
    (M depth : ℕ) [NeZero M]
    (i : CMP99SectionCHeterogeneousIndex j) :
    Fintype (D.generatedSectionCHeterogeneousCoordinateSite hpi5 M depth i) := by
  rcases i with ⟨s, kind⟩
  cases kind <;>
    simp only [generatedSectionCHeterogeneousCoordinateSite] <;>
    infer_instance

noncomputable instance generatedSectionCHeterogeneousCoordinateSiteDecidableEq
    (D : CMP99SourceDependentOmegaGeometry
      (FinBox 4 (2 * Q)) j ScaleSite Scaled
      (cmp99SourceTildePiLargeBlocks cell 3)
      (cmp99SourceTildePiLargeBlocks cell 4) dist gap)
    (hpi5 : D.fineRegion (cmp99OmegaZeroIndex j) ⊆
      cmp99SourceTildePiLargeBlocks cell 5)
    (M depth : ℕ) [NeZero M]
    (i : CMP99SectionCHeterogeneousIndex j) :
    DecidableEq
      (D.generatedSectionCHeterogeneousCoordinateSite hpi5 M depth i) := by
  rcases i with ⟨s, kind⟩
  cases kind <;>
    simp only [generatedSectionCHeterogeneousCoordinateSite] <;>
    infer_instance

/-- Embed every heterogeneous coordinate in the common fine periodic box.
For a coarse coordinate this is the canonical representative of its
terminal block. -/
noncomputable def generatedSectionCHeterogeneousFineCoordinate
    (D : CMP99SourceDependentOmegaGeometry
      (FinBox 4 (2 * Q)) j ScaleSite Scaled
      (cmp99SourceTildePiLargeBlocks cell 3)
      (cmp99SourceTildePiLargeBlocks cell 4) dist gap)
    (hpi5 : D.fineRegion (cmp99OmegaZeroIndex j) ⊆
      cmp99SourceTildePiLargeBlocks cell 5)
    (M depth : ℕ) [NeZero M]
    (i : CMP99SectionCHeterogeneousIndex j) :
    D.generatedSectionCHeterogeneousCoordinateSite hpi5 M depth i →
      FinBox 4 (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)) := by
  rcases i with ⟨s, kind⟩
  let Omega := D.operatorCoarseRegion hpi5 s
  let regions := cmp99SourceIteratedLiftActiveRegionChain
    (M := M) Omega (depth + 1)
  cases kind with
  | coarse =>
      intro x
      change regions.terminalSite at x
      exact (regions.terminalRepresentative x).1
  | fine =>
      intro x
      change ActiveGaugeRegion.Site
        (cmp99IteratedLiftActiveRegion (M := M) Omega (depth + 1)) at x
      exact x.1

/-- Cross-carrier distance obtained by embedding both endpoints in the same
fine periodic box. -/
noncomputable def generatedSectionCHeterogeneousCoordinateDist
    (D : CMP99SourceDependentOmegaGeometry
      (FinBox 4 (2 * Q)) j ScaleSite Scaled
      (cmp99SourceTildePiLargeBlocks cell 3)
      (cmp99SourceTildePiLargeBlocks cell 4) dist gap)
    (hpi5 : D.fineRegion (cmp99OmegaZeroIndex j) ⊆
      cmp99SourceTildePiLargeBlocks cell 5)
    (M depth : ℕ) [NeZero M]
    (r s : CMP99SectionCHeterogeneousIndex j) :
    D.generatedSectionCHeterogeneousCoordinateSite hpi5 M depth s →
      D.generatedSectionCHeterogeneousCoordinateSite hpi5 M depth r → ℕ :=
  fun target source => finBoxDist
    (D.generatedSectionCHeterogeneousFineCoordinate hpi5 M depth s target)
    (D.generatedSectionCHeterogeneousFineCoordinate hpi5 M depth r source)

@[simp] theorem generatedSectionCHeterogeneousCoordinateDist_self
    (D : CMP99SourceDependentOmegaGeometry
      (FinBox 4 (2 * Q)) j ScaleSite Scaled
      (cmp99SourceTildePiLargeBlocks cell 3)
      (cmp99SourceTildePiLargeBlocks cell 4) dist gap)
    (hpi5 : D.fineRegion (cmp99OmegaZeroIndex j) ⊆
      cmp99SourceTildePiLargeBlocks cell 5)
    (M depth : ℕ) [NeZero M]
    (r : CMP99SectionCHeterogeneousIndex j)
    (x : D.generatedSectionCHeterogeneousCoordinateSite hpi5 M depth r) :
    D.generatedSectionCHeterogeneousCoordinateDist hpi5 M depth r r x x = 0 := by
  exact finBoxDist_self _

theorem generatedSectionCHeterogeneousCoordinateDist_triangle
    (D : CMP99SourceDependentOmegaGeometry
      (FinBox 4 (2 * Q)) j ScaleSite Scaled
      (cmp99SourceTildePiLargeBlocks cell 3)
      (cmp99SourceTildePiLargeBlocks cell 4) dist gap)
    (hpi5 : D.fineRegion (cmp99OmegaZeroIndex j) ⊆
      cmp99SourceTildePiLargeBlocks cell 5)
    (M depth : ℕ) [NeZero M]
    (r s t : CMP99SectionCHeterogeneousIndex j)
    (target : D.generatedSectionCHeterogeneousCoordinateSite hpi5 M depth t)
    (middle : D.generatedSectionCHeterogeneousCoordinateSite hpi5 M depth s)
    (source : D.generatedSectionCHeterogeneousCoordinateSite hpi5 M depth r) :
    D.generatedSectionCHeterogeneousCoordinateDist hpi5 M depth r t
        target source ≤
      D.generatedSectionCHeterogeneousCoordinateDist hpi5 M depth s t
          target middle +
        D.generatedSectionCHeterogeneousCoordinateDist hpi5 M depth r s
          middle source := by
  exact finBoxDist_triangle _ _ _

/-- Fixed-rate amplitude selected by each of the two displayed basic
species. -/
noncomputable def generatedCMP95SectionCHeterogeneousLabelWeightedRowAmplitude
    (P : CMP95SourceSmoothPartitionProfile)
    (M depth : ℕ) (spacing epsilon rate : ℝ)
    {r s : CMP99SectionCHeterogeneousIndex j} :
    GeneratedSectionCHeterogeneousLabel j r s → ℝ
  | .basic _ =>
      cmp99SourceGeneratedSmoothFineBasicWeightedRowAmplitude
        P M depth spacing epsilon rate
  | .basicAdjoint _ =>
      cmp99SourceGeneratedSmoothBasicAdjointWeightedRowAmplitude
        P M depth spacing epsilon rate

/-- Coordinate-exposed interpretation of the two displayed heterogeneous
labels.  The adjoint label is the literal recursively generated weighted
adjoint, transported through the proved terminal-bundle equality. -/
noncomputable def generatedCMP95SectionCHeterogeneousCoordinateLabelOperator
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
    {r s : CMP99SectionCHeterogeneousIndex j} :
    GeneratedSectionCHeterogeneousLabel j r s →
      DependentFinitePiLpArrow
        (D.generatedSectionCHeterogeneousCoordinateSite hpi5 M depth)
        (SUNLieCoord Nc) r s := by
  intro label
  cases label with
  | basic t =>
      simpa [generatedSectionCHeterogeneousCoordinateSite] using
        D.generatedCMP95SourceCenteredSmoothFineSectionCBasicFactor P
          hpi5 t hM depth hspacing background budget fineSmall hsmall
  | basicAdjoint t =>
      simpa [generatedSectionCHeterogeneousCoordinateSite] using
        D.generatedCMP95SourceCenteredSmoothPhysicalBasicAdjointFactor P
          hpi5 t hM depth hspacing background budget fineSmall hsmall

/-- Each displayed heterogeneous label carries its proved fixed-rate row in
the common physical coordinate metric. -/
theorem generatedCMP95SectionCHeterogeneousCoordinateLabelOperator_weightedRow
    (D : CMP99SourceDependentOmegaGeometry
      (FinBox 4 (2 * Q)) j ScaleSite Scaled
      (cmp99SourceTildePiLargeBlocks cell 3)
      (cmp99SourceTildePiLargeBlocks cell 4) dist gap)
    (P : CMP95SourceSmoothPartitionProfile)
    (hpi5 : D.fineRegion (cmp99OmegaZeroIndex j) ⊆
      cmp99SourceTildePiLargeBlocks cell 5)
    (hM : 2 ≤ M) (depth : ℕ)
    {spacing epsilon rate : ℝ} (hspacing : 0 < spacing) (hrate : 0 < rate)
    (hrateLt : rate < cmp99SourceGeneratedCombesThomasRate
      4 M depth spacing epsilon / 2)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 M Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff 4 M (depth + 1)
      spacing epsilon < 1)
    {r s : CMP99SectionCHeterogeneousIndex j}
    (label : GeneratedSectionCHeterogeneousLabel j r s) :
    FinitePiLpTypedWeightedRowKernelBound
      (D.generatedCMP95SectionCHeterogeneousCoordinateLabelOperator P hpi5
        hM depth hspacing background budget fineSmall hsmall label)
      (D.generatedSectionCHeterogeneousCoordinateDist hpi5 M depth r s)
      (generatedCMP95SectionCHeterogeneousLabelWeightedRowAmplitude
        P M depth spacing epsilon rate label) rate := by
  cases label with
  | basic t =>
      simpa [generatedCMP95SectionCHeterogeneousCoordinateLabelOperator,
        generatedCMP95SectionCHeterogeneousLabelWeightedRowAmplitude,
        generatedSectionCHeterogeneousCoordinateDist,
        generatedSectionCHeterogeneousFineCoordinate,
        generatedSectionCHeterogeneousCoordinateSite] using
        D.generatedCMP95SourceCenteredSmoothFineSectionCBasicFactor_weightedRow
          P hpi5 t hM depth hspacing hrate hrateLt background budget fineSmall
            hsmall
  | basicAdjoint t =>
      simpa [generatedCMP95SectionCHeterogeneousCoordinateLabelOperator,
        generatedCMP95SectionCHeterogeneousLabelWeightedRowAmplitude,
        generatedSectionCHeterogeneousCoordinateDist,
        generatedSectionCHeterogeneousFineCoordinate,
        generatedSectionCHeterogeneousCoordinateSite] using
        D.generatedCMP95SourceCenteredSmoothPhysicalBasicAdjointFactor_weightedRow
          P hpi5 t hM depth hspacing hrate hrateLt background budget fineSmall
            hsmall

/-- Every well-typed word in the two displayed heterogeneous species
preserves one spatial rate.  Its amplitude is the literal ordered product of
the factorwise physical budgets. -/
theorem generatedCMP95SectionCHeterogeneousCoordinateOperatorWalk_weightedRow
    (D : CMP99SourceDependentOmegaGeometry
      (FinBox 4 (2 * Q)) j ScaleSite Scaled
      (cmp99SourceTildePiLargeBlocks cell 3)
      (cmp99SourceTildePiLargeBlocks cell 4) dist gap)
    (P : CMP95SourceSmoothPartitionProfile)
    (hpi5 : D.fineRegion (cmp99OmegaZeroIndex j) ⊆
      cmp99SourceTildePiLargeBlocks cell 5)
    (hM : 2 ≤ M) (depth : ℕ)
    {spacing epsilon rate : ℝ} (hspacing : 0 < spacing) (hrate : 0 < rate)
    (hrateLt : rate < cmp99SourceGeneratedCombesThomasRate
      4 M depth spacing epsilon / 2)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 M Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff 4 M (depth + 1)
      spacing epsilon < 1)
    {r s : CMP99SectionCHeterogeneousIndex j}
    (walk : DependentArrowWalk (GeneratedSectionCHeterogeneousLabel j) r s) :
    FinitePiLpTypedWeightedRowKernelBound
      (dependentFinitePiLpWalkOperator
        (D.generatedSectionCHeterogeneousCoordinateSite hpi5 M depth)
        (SUNLieCoord Nc)
        (walk.map
          (D.generatedCMP95SectionCHeterogeneousCoordinateLabelOperator P hpi5
            hM depth hspacing background budget fineSmall hsmall)))
      (D.generatedSectionCHeterogeneousCoordinateDist hpi5 M depth r s)
      (walk.amplitude
        (generatedCMP95SectionCHeterogeneousLabelWeightedRowAmplitude
          P M depth spacing epsilon rate)) rate := by
  exact dependentFinitePiLpWalkOperator_map_weightedRowKernelBound
    (D.generatedSectionCHeterogeneousCoordinateSite hpi5 M depth)
    (SUNLieCoord Nc) (GeneratedSectionCHeterogeneousLabel j)
    (D.generatedSectionCHeterogeneousCoordinateDist hpi5 M depth)
    (D.generatedSectionCHeterogeneousCoordinateDist_self hpi5 M depth)
    (D.generatedSectionCHeterogeneousCoordinateDist_triangle hpi5 M depth)
    (D.generatedCMP95SectionCHeterogeneousCoordinateLabelOperator P hpi5 hM
      depth hspacing background budget fineSmall hsmall)
    (generatedCMP95SectionCHeterogeneousLabelWeightedRowAmplitude
      P M depth spacing epsilon rate)
    hrate.le
    (fun label =>
      D.generatedCMP95SectionCHeterogeneousCoordinateLabelOperator_weightedRow
        P hpi5 hM depth hspacing hrate hrateLt background budget fineSmall
          hsmall label)
    walk

/-- Pointwise `(3.108)`-shaped consequence for every well-typed word in the
two displayed heterogeneous source species. -/
theorem generatedCMP95SectionCHeterogeneousCoordinateOperatorWalk_exponential
    (D : CMP99SourceDependentOmegaGeometry
      (FinBox 4 (2 * Q)) j ScaleSite Scaled
      (cmp99SourceTildePiLargeBlocks cell 3)
      (cmp99SourceTildePiLargeBlocks cell 4) dist gap)
    (P : CMP95SourceSmoothPartitionProfile)
    (hpi5 : D.fineRegion (cmp99OmegaZeroIndex j) ⊆
      cmp99SourceTildePiLargeBlocks cell 5)
    (hM : 2 ≤ M) (depth : ℕ)
    {spacing epsilon rate : ℝ} (hspacing : 0 < spacing) (hrate : 0 < rate)
    (hrateLt : rate < cmp99SourceGeneratedCombesThomasRate
      4 M depth spacing epsilon / 2)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 M Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff 4 M (depth + 1)
      spacing epsilon < 1)
    {r s : CMP99SectionCHeterogeneousIndex j}
    (walk : DependentArrowWalk (GeneratedSectionCHeterogeneousLabel j) r s) :
    FinitePiLpTypedExponentialKernelBound
      (dependentFinitePiLpWalkOperator
        (D.generatedSectionCHeterogeneousCoordinateSite hpi5 M depth)
        (SUNLieCoord Nc)
        (walk.map
          (D.generatedCMP95SectionCHeterogeneousCoordinateLabelOperator P hpi5
            hM depth hspacing background budget fineSmall hsmall)))
      (D.generatedSectionCHeterogeneousCoordinateDist hpi5 M depth r s)
      (walk.amplitude
        (generatedCMP95SectionCHeterogeneousLabelWeightedRowAmplitude
          P M depth spacing epsilon rate)) rate :=
  finitePiLpTypedExponentialKernelBound_of_weightedRow _ _ hrate
    (D.generatedCMP95SectionCHeterogeneousCoordinateOperatorWalk_weightedRow
      P hpi5 hM depth hspacing hrate hrateLt background budget fineSmall
        hsmall walk)

end CMP99SourceDependentOmegaGeometry

end
end YangMills.RG
