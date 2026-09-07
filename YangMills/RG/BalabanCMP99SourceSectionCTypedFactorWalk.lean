/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceGeneratedSectionCSourceCutTower
import YangMills.RG.BalabanCMP99SourceGeneratedSectionCCommutatorFactor

/-!
# Source-typed Section C factor walks

After CMP99 (3.99), the paper states explicitly that the factors `R'_alpha(X)`
may act between different scales and that not every sequence of indices is
admissible.  This indexed label family records that fact in the type.

The constructor `cut` is the physically reconstructed factor (3.97), and can
only label the consecutive transition `r -> r+1`.  The constructor
`commutator` is the explicitly printed same-scale factor
`tildeChi Q' [G',(h')²]G'Q'^*h C h` on p. 412.  The constructor `other` keeps
the paper's non-exhaustive "etc." family open, but also requires every future
species to declare its source and target scales.  Thus no endomorphism padding
or fabricated exhaustive enumeration is introduced.

The terminal theorem identifies the label walk consisting of all consecutive
`cut` factors with the already constructed source-generated rectangular
tower, exactly and without casts.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator RealInnerProductSpace

noncomputable section

universe u v

/-- A source- and target-indexed Section C label alphabet.  Only the literal
factor (3.97) is closed; the source's remaining non-exhaustive possibilities
stay in the indexed family `Other`. -/
inductive CMP99SectionCTypedFactorLabel (j : ℕ)
    (Other : Fin (j + 2) → Fin (j + 2) → Type u) :
    Fin (j + 2) → Fin (j + 2) → Type u where
  | cut (r : Fin (j + 1)) :
      CMP99SectionCTypedFactorLabel j Other r.castSucc r.succ
  | commutator (s : Fin (j + 2)) :
      CMP99SectionCTypedFactorLabel j Other s s
  | other {r s : Fin (j + 2)} (alpha : Other r s) :
      CMP99SectionCTypedFactorLabel j Other r s

/-- The cut-only label path through the `j+1` printed regional transitions. -/
def cmp99SectionCSourceCutLabelTower (j : ℕ) :
    DependentArrowWalk
      (CMP99SectionCTypedFactorLabel j (fun _ _ => Empty))
      (cmp99OmegaZeroIndex j) (cmp99OmegaLastIndex j) :=
  DependentArrowWalk.finSuccPath fun r =>
    CMP99SectionCTypedFactorLabel.cut r

@[simp] theorem cmp99SectionCSourceCutLabelTower_length (j : ℕ) :
    (cmp99SectionCSourceCutLabelTower j).length = j + 1 := by
  exact DependentArrowWalk.length_finSuccPath _

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

/-- Interpret the two reconstructed printed species by their literal
source-generated operators.  The impossible open branch is eliminated from
`Empty`. -/
noncomputable def generatedSectionCSourceCutLabelOperator
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
    {r s : Fin (j + 2)} :
    CMP99SectionCTypedFactorLabel j (fun _ _ => Empty) r s →
      DependentFinitePiLpArrow (D.GeneratedSectionCCoarseSiteFamily hpi5)
        (SUNLieCoord Nc) r s
  | .cut k =>
      D.generatedSectionCCutTowerStep hpi5
        (fun t => D.generatedSectionCSourceTransitionCutData P hpi5 t)
        hM depth hspacing background budget fineSmall hsmall k
  | .commutator t =>
      D.generatedPhysicalCoarseSectionCCommutatorFactorCoordinates P hpi5 t
        hM depth hspacing background budget fineSmall hsmall
  | .other alpha => nomatch alpha

/-- The physical operator walk obtained by interpreting the typed cut-label
walk factor by factor. -/
noncomputable def generatedSectionCSourceCutLabeledOperatorWalk
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
      spacing epsilon < 1) :=
  (cmp99SectionCSourceCutLabelTower j).map
    (D.generatedSectionCSourceCutLabelOperator P hpi5 hM depth hspacing
      background budget fineSmall hsmall)

/-- Literal dependent-walk identification: interpreting the source labels of
the consecutive (3.97) factors gives exactly the previously generated
physical tower. -/
theorem generatedSectionCSourceCutLabeledOperatorWalk_eq_factorTower
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
      spacing epsilon < 1) :
    D.generatedSectionCSourceCutLabeledOperatorWalk P hpi5 hM depth hspacing
        background budget fineSmall hsmall =
      D.generatedSectionCSourceCutFactorTower P hpi5 hM depth hspacing
        background budget fineSmall hsmall := by
  unfold generatedSectionCSourceCutLabeledOperatorWalk
    cmp99SectionCSourceCutLabelTower
    generatedSectionCSourceCutFactorTower
    generatedSectionCCutFactorTower
  simpa only [generatedSectionCSourceCutLabelOperator] using
    (DependentArrowWalk.map_finSuccPath
      (f := fun {r s}
        (label : CMP99SectionCTypedFactorLabel j
          (fun _ _ => Empty) r s) =>
        D.generatedSectionCSourceCutLabelOperator P hpi5 hM depth
          hspacing background budget fineSmall hsmall label)
      (step := fun r : Fin (j + 1) =>
        CMP99SectionCTypedFactorLabel.cut
          (Other := fun _ _ => Empty) r))

end CMP99SourceDependentOmegaGeometry

end

end YangMills.RG
