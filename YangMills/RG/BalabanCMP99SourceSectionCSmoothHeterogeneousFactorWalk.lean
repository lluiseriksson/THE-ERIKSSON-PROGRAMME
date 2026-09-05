/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceSectionCHeterogeneousFactorWalk
import YangMills.RG.BalabanCMP99SourceGeneratedSectionCSmoothBasicFactor
import YangMills.RG.DependentFinitePiLpWeightedRowWalk

/-!
# Smooth heterogeneous CMP99 Section C walks

CMP99 printed pp. 412--413 explicitly composes factors which may change
carrier.  This module interprets the two reconstructed heterogeneous species

* `K(h'_Pi) G'_Pi h'_Pi`, and
* `K(h'_Pi) G'_Pi h'_Pi Q'^*`

using one CMP95 (1.118) profile.  The resulting walk is definitionally typed
through the genuine fine/coarse Hilbert bundles, and its operator norm is
bounded by the ordered product of the source-derived `M0^-1` amplitudes.

Honest scope: this closes the two displayed basic species; it does not treat
the printed word “etc.” as an exhaustive list.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator RealInnerProductSpace

noncomputable section

universe u v

namespace DependentArrowWalk

/-- A product of nonnegative factor amplitudes is nonnegative along every
genuinely typed walk. -/
theorem amplitude_nonneg {ι : Type u} {Label : ι → ι → Type v}
    (amplitude : ∀ {r s}, Label r s → ℝ)
    (hamplitude : ∀ {r s} (label : Label r s), 0 ≤ amplitude label)
    {r s : ι} (walk : DependentArrowWalk Label r s) :
    0 ≤ walk.amplitude amplitude := by
  induction walk with
  | nil => simp
  | cons head tail ih =>
      exact mul_nonneg ih (hamplitude head)

end DependentArrowWalk

/-- Operator norms multiply along a genuinely dependent Hilbert-space walk. -/
theorem norm_dependentBundledHilbertWalkOperator_map_le
    {ι : Type u}
    (Space : ι → CMP99SourceWeightedTowerHilbertSpace)
    {Label : ι → ι → Type v}
    (operator : ∀ {r s}, Label r s →
      DependentBundledHilbertArrow Space r s)
    (amplitude : ∀ {r s}, Label r s → ℝ)
    (hamplitude : ∀ {r s} (label : Label r s),
      0 ≤ amplitude label)
    (hnorm : ∀ {r s} (label : Label r s),
      ‖operator label‖ ≤ amplitude label)
    {r s : ι} (walk : DependentArrowWalk Label r s) :
    ‖dependentBundledHilbertWalkOperator Space (walk.map operator)‖ ≤
      walk.amplitude amplitude := by
  induction walk with
  | nil i =>
      simp only [DependentArrowWalk.map_nil, DependentArrowWalk.amplitude_nil,
        dependentBundledHilbertWalkOperator]
      exact ContinuousLinearMap.norm_id_le
  | @cons i k l head tail ih =>
      simp only [DependentArrowWalk.map_cons, DependentArrowWalk.amplitude_cons,
        dependentBundledHilbertWalkOperator, DependentArrowWalk.evaluate_cons]
      calc
        ‖(tail.map operator).evaluate
            (fun q => ContinuousLinearMap.id ℝ (Space q).carrier)
            (fun f h => f.comp h) |>.comp (operator head)‖ ≤
            ‖(tail.map operator).evaluate
              (fun q => ContinuousLinearMap.id ℝ (Space q).carrier)
              (fun f h => f.comp h)‖ * ‖operator head‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ tail.amplitude amplitude * amplitude head :=
          mul_le_mul ih (hnorm head) (norm_nonneg _) (by
            exact tail.amplitude_nonneg amplitude hamplitude)

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

/-- Source-derived factorwise norm amplitude for the two displayed
heterogeneous species. -/
noncomputable def generatedCMP95SectionCHeterogeneousLabelNormAmplitude
    (P : CMP95SourceSmoothPartitionProfile)
    (M depth : ℕ) (spacing epsilon : ℝ)
    {r s : CMP99SectionCHeterogeneousIndex j} :
    GeneratedSectionCHeterogeneousLabel j r s → ℝ
  | .basic _ =>
      cmp99SourceGeneratedSmoothFineBasicFactorNormBound
        P M depth spacing epsilon
  | .basicAdjoint _ =>
      cmp99SourceGeneratedSmoothBasicAdjointFactorNormBound
        P M depth spacing epsilon

/-- Interpret the two displayed heterogeneous labels using one CMP95 smooth
profile and the genuine generated source tower. -/
noncomputable def generatedCMP95SectionCHeterogeneousLabelOperator
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
      DependentBundledHilbertArrow
        (D.generatedSectionCHeterogeneousSpace hpi5 hM depth spacing epsilon
          background budget fineSmall) r s := by
  intro label
  cases label with
  | basic t =>
      exact D.generatedCMP95SourceCenteredSmoothFineSectionCBasicFactor P
        hpi5 t hM depth hspacing background budget fineSmall hsmall
  | basicAdjoint t =>
      exact D.generatedCMP95SourceCenteredSmoothSectionCBasicAdjointFactor P
        hpi5 t hM depth hspacing background budget fineSmall hsmall

/-- Each reconstructed heterogeneous source label carries its proved
`M0^-1` norm budget. -/
theorem norm_generatedCMP95SectionCHeterogeneousLabelOperator_le
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
    {r s : CMP99SectionCHeterogeneousIndex j}
    (label : GeneratedSectionCHeterogeneousLabel j r s) :
    ‖D.generatedCMP95SectionCHeterogeneousLabelOperator P hpi5 hM depth
      hspacing background budget fineSmall hsmall label‖ ≤
      generatedCMP95SectionCHeterogeneousLabelNormAmplitude
        P M depth spacing epsilon label := by
  cases label with
  | basic t =>
      exact D.norm_generatedCMP95SourceCenteredSmoothFineSectionCBasicFactor_le
        P hpi5 t hM depth hspacing background budget fineSmall hsmall
  | basicAdjoint t =>
      exact D.norm_generatedCMP95SourceCenteredSmoothSectionCBasicAdjointFactor_le
        P hpi5 t hM depth hspacing background budget fineSmall hsmall

/-- Every well-typed word in the two displayed heterogeneous source species
has norm bounded by the literal ordered product of their derived budgets. -/
theorem norm_generatedCMP95SectionCHeterogeneousOperatorWalk_le
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
    {r s : CMP99SectionCHeterogeneousIndex j}
    (walk : DependentArrowWalk (GeneratedSectionCHeterogeneousLabel j) r s) :
    ‖dependentBundledHilbertWalkOperator
      (D.generatedSectionCHeterogeneousSpace hpi5 hM depth spacing epsilon
        background budget fineSmall)
      (walk.map (D.generatedCMP95SectionCHeterogeneousLabelOperator P hpi5 hM
        depth hspacing background budget fineSmall hsmall))‖ ≤
      walk.amplitude
        (generatedCMP95SectionCHeterogeneousLabelNormAmplitude
          P M depth spacing epsilon) := by
  apply norm_dependentBundledHilbertWalkOperator_map_le
  · intro a b label
    exact (norm_nonneg
      (D.generatedCMP95SectionCHeterogeneousLabelOperator P hpi5 hM depth
        hspacing background budget fineSmall hsmall label)).trans
      (D.norm_generatedCMP95SectionCHeterogeneousLabelOperator_le P hpi5 hM
        depth hspacing background budget fineSmall hsmall label)
  · exact fun label =>
      D.norm_generatedCMP95SectionCHeterogeneousLabelOperator_le P hpi5 hM
        depth hspacing background budget fineSmall hsmall label

end CMP99SourceDependentOmegaGeometry

end
end YangMills.RG
