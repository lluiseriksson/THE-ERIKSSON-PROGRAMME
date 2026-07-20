/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceGeneratedSectionCBasicAdjointFactor
import YangMills.RG.DependentArrowWalk

/-!
# Heterogeneous Section C factor walks

CMP99 printed p. 413 warns that the factors in the generalized random-walk
expansion need not act on one common space.  Its explicit example

`K(h'_Pi) G'_Pi h'_Pi Q'^*`

maps the terminal coarse `B` field to the fine `eta` field.  This file records
that change of carrier in the index of a dependent arrow.  The coarse member
is the actual generated terminal Hilbert bundle and the fine member is the
actual lifted regional field bundle.  Consequently the printed mixed-scale
factor typechecks without an ambient zero extension or a dependent transport.

This is a typing and source-identification result.  It does not assert the
sharper `O(M^-1)` bound of (3.89), which needs the smooth-partition estimates
imported by CMP99 from Sect. A of the preceding propagator paper.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator RealInnerProductSpace

noncomputable section

universe u v

/-- The two physical carriers that occur at a fixed Section C scale. -/
inductive CMP99SectionCCarrierKind where
  | coarse
  | fine
deriving DecidableEq

/-- A scale together with its physical coarse/fine carrier. -/
abbrev CMP99SectionCHeterogeneousIndex (j : ℕ) :=
  Fin (j + 2) × CMP99SectionCCarrierKind

/-- Continuous linear arrows between a family of bundled Hilbert spaces. -/
abbrev DependentBundledHilbertArrow {ι : Type u}
    (Space : ι → CMP99SourceWeightedTowerHilbertSpace) (r s : ι) :=
  (Space r).carrier →L[ℝ] (Space s).carrier

/-- Evaluate a dependent walk of genuine rectangular Hilbert-space arrows. -/
noncomputable def dependentBundledHilbertWalkOperator {ι : Type u}
    (Space : ι → CMP99SourceWeightedTowerHilbertSpace)
    {r s : ι}
    (walk : DependentArrowWalk (DependentBundledHilbertArrow Space) r s) :
    DependentBundledHilbertArrow Space r s :=
  walk.evaluate
    (fun i => ContinuousLinearMap.id ℝ (Space i).carrier)
    (fun f h => f.comp h)

@[simp] theorem dependentBundledHilbertWalkOperator_singleton {ι : Type u}
    (Space : ι → CMP99SourceWeightedTowerHilbertSpace)
    {r s : ι} (A : DependentBundledHilbertArrow Space r s) :
    dependentBundledHilbertWalkOperator Space
      (.cons A (.nil s)) = A := by
  exact DependentArrowWalk.evaluate_singleton
    (fun i => ContinuousLinearMap.id ℝ (Space i).carrier)
    (fun f h => f.comp h)
    (fun f => by ext x; rfl)
    A

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
set_option maxHeartbeats 5000000

/-- The literal generated Hilbert bundle selected by a scale and a
coarse/fine tag.  No equality transport occurs in this definition. -/
noncomputable def generatedSectionCHeterogeneousSpace
    (D : CMP99SourceDependentOmegaGeometry
      (FinBox 4 (2 * Q)) j ScaleSite Scaled
      (cmp99SourceTildePiLargeBlocks cell 3)
      (cmp99SourceTildePiLargeBlocks cell 4) dist gap)
    (hpi5 : D.fineRegion (cmp99OmegaZeroIndex j) ⊆
      cmp99SourceTildePiLargeBlocks cell 5)
    (hM : 2 ≤ M) (depth : ℕ) (spacing epsilon : ℝ)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 M Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (i : CMP99SectionCHeterogeneousIndex j) :
    CMP99SourceWeightedTowerHilbertSpace := by
  let Omega := D.operatorCoarseRegion hpi5 i.1
  let regions := cmp99SourceIteratedLiftActiveRegionChain (M := M)
    Omega (depth + 1)
  match i.2 with
  | .coarse =>
      exact (regions.weightedQprimeTower (show 2 ≤ 4 by norm_num) hM
        (matrixSUNAdjointModel Nc) spacing epsilon background
        budget.toRadiusChain fineSmall).TerminalSpace
  | .fine =>
      exact cmp99SourcePhysicalTerminalHilbertSpace Nc
        (cmp99IteratedLiftActiveRegion (M := M) Omega (depth + 1))

/-- The closed source alphabet presently realized on the heterogeneous
carriers.  `basicAdjoint` is the explicit mixed-scale species on p. 413;
`basic` is the p. 412 fine endomorphism before its optional `Q'^*` tail. -/
inductive GeneratedSectionCHeterogeneousLabel (j : ℕ) :
    CMP99SectionCHeterogeneousIndex j →
      CMP99SectionCHeterogeneousIndex j → Type where
  | basic (s : Fin (j + 2)) :
      GeneratedSectionCHeterogeneousLabel j (s, .fine) (s, .fine)
  | basicAdjoint (s : Fin (j + 2)) :
      GeneratedSectionCHeterogeneousLabel j (s, .coarse) (s, .fine)

/-- Interpret the two printed labels by the already generated physical
operators on their literal carriers. -/
noncomputable def generatedSectionCHeterogeneousLabelOperator
    (D : CMP99SourceDependentOmegaGeometry
      (FinBox 4 (2 * Q)) j ScaleSite Scaled
      (cmp99SourceTildePiLargeBlocks cell 3)
      (cmp99SourceTildePiLargeBlocks cell 4) dist gap)
    (P : CMP99SourceSquarePartition Q)
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
      exact D.generatedPhysicalFineSectionCBasicFactor P hpi5 t hM depth
        hspacing background budget fineSmall hsmall
  | basicAdjoint t =>
      exact D.generatedPhysicalSectionCBasicAdjointFactor P hpi5 t hM depth
        hspacing background budget fineSmall hsmall

/-- The one-factor dependent walk carrying the literal coarse-to-fine arrow
from CMP99 printed p. 413. -/
def generatedSectionCBasicAdjointLabelWalk (s : Fin (j + 2)) :
    DependentArrowWalk (GeneratedSectionCHeterogeneousLabel j)
      (s, .coarse) (s, .fine) :=
  .cons (.basicAdjoint s)
    (.nil (s, CMP99SectionCCarrierKind.fine))

/-- Interpreting the printed mixed-scale label gives exactly the constructed
physical factor, not a transported or zero-extended surrogate. -/
theorem generatedSectionCBasicAdjointLabelWalk_eq_source
    (D : CMP99SourceDependentOmegaGeometry
      (FinBox 4 (2 * Q)) j ScaleSite Scaled
      (cmp99SourceTildePiLargeBlocks cell 3)
      (cmp99SourceTildePiLargeBlocks cell 4) dist gap)
    (P : CMP99SourceSquarePartition Q)
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
    dependentBundledHilbertWalkOperator
      (D.generatedSectionCHeterogeneousSpace hpi5 hM depth spacing epsilon
        background budget fineSmall)
      ((generatedSectionCBasicAdjointLabelWalk s).map
        (D.generatedSectionCHeterogeneousLabelOperator P hpi5 hM depth
          hspacing background budget fineSmall hsmall)) =
      D.generatedPhysicalSectionCBasicAdjointFactor P hpi5 s hM depth
        hspacing background budget fineSmall hsmall := by
  rfl

end CMP99SourceDependentOmegaGeometry

end
end YangMills.RG
