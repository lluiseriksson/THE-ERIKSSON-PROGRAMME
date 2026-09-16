/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceRegionalSectionCCutFactor
import YangMills.RG.DependentArrowWalk

/-!
# Scale-typed regional Section C walks

The factors in CMP99 Section C may act between different regional scales.
This module instantiates the dependent-arrow walk with the actual regional
coarse Hilbert spaces and inserts the cut one-step factor without extending it
to an ambient endomorphism.
-/

namespace YangMills.RG

noncomputable section

variable {Q M j Nc : ℕ} [NeZero Q] [NeZero M] [NeZero Nc]
variable {cell : FinBox 4 Q}

/-- A continuous linear arrow between two genuine regional coarse fields. -/
abbrev CMP99OmegaRegionalCoarseArrow
    (Seq : CMP99SourceOmegaGeometry cell j) (r s : Fin (j + 2)) :=
  CMP99OmegaRegionalCoarseField (M := M) Seq r (SUNLieCoord Nc) →L[ℝ]
    CMP99OmegaRegionalCoarseField (M := M) Seq s (SUNLieCoord Nc)

/-- A walk through the actual scale-indexed regional coarse fields. -/
abbrev CMP99OmegaRegionalCoarseOperatorWalk
    (Seq : CMP99SourceOmegaGeometry cell j) (r s : Fin (j + 2)) :=
  DependentArrowWalk
    (fun r s => CMP99OmegaRegionalCoarseArrow (M := M) (Nc := Nc) Seq r s) r s

/-- Identity arrow for the physical regional coarse family. -/
noncomputable def cmp99OmegaRegionalCoarseArrowIdentity
    (Seq : CMP99SourceOmegaGeometry cell j) (r : Fin (j + 2)) :
    CMP99OmegaRegionalCoarseArrow (M := M) (Nc := Nc) Seq r r :=
  ContinuousLinearMap.id ℝ _

/-- Typed composition for physical regional coarse arrows. -/
noncomputable def cmp99OmegaRegionalCoarseArrowCompose
    (Seq : CMP99SourceOmegaGeometry cell j) {r s t : Fin (j + 2)}
    (f : CMP99OmegaRegionalCoarseArrow (M := M) (Nc := Nc) Seq s t)
    (g : CMP99OmegaRegionalCoarseArrow (M := M) (Nc := Nc) Seq r s) :
    CMP99OmegaRegionalCoarseArrow (M := M) (Nc := Nc) Seq r t :=
  f.comp g

/-- Exactly typed operator represented by a regional Section C walk. -/
noncomputable def CMP99OmegaRegionalCoarseOperatorWalk.operator
    (Seq : CMP99SourceOmegaGeometry cell j) {r s : Fin (j + 2)}
    (walk : CMP99OmegaRegionalCoarseOperatorWalk (M := M) (Nc := Nc) Seq r s) :
    CMP99OmegaRegionalCoarseArrow (M := M) (Nc := Nc) Seq r s :=
  walk.evaluate (cmp99OmegaRegionalCoarseArrowIdentity Seq)
    (fun f g => cmp99OmegaRegionalCoarseArrowCompose Seq f g)

/-- The literal cut (3.97) core as a one-step walk from the larger regional
carrier to the consecutive smaller carrier. -/
noncomputable def cmp99OmegaSourcePhysicalOneStepSectionCCutFactorWalk
    (Seq : CMP99SourceOmegaGeometry cell j) (r : Fin (j + 1))
    (Cuts : CMP99SourceSectionCTransitionCutData (M := M) Seq r)
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground 4 (M * (2 * Q)) Nc)
    {spacing a : ℝ} (hspacing : 0 < spacing) (ha : 0 < a) :
    CMP99OmegaRegionalCoarseOperatorWalk (M := M) (Nc := Nc) Seq
      (cmp99OmegaTransitionIndex r) (cmp99OmegaTransitionNextIndex r) :=
  DependentArrowWalk.cons
    (cmp99OmegaSourcePhysicalOneStepSectionCCutFactor
      Seq r Cuts rho U hspacing ha)
    (DependentArrowWalk.nil _)

/-- Evaluation of the one-step scale-typed walk is definitionally the physical
cut regional factor. -/
theorem cmp99OmegaSourcePhysicalOneStepSectionCCutFactorWalk_operator
    (Seq : CMP99SourceOmegaGeometry cell j) (r : Fin (j + 1))
    (Cuts : CMP99SourceSectionCTransitionCutData (M := M) Seq r)
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground 4 (M * (2 * Q)) Nc)
    {spacing a : ℝ} (hspacing : 0 < spacing) (ha : 0 < a) :
    (cmp99OmegaSourcePhysicalOneStepSectionCCutFactorWalk
      Seq r Cuts rho U hspacing ha).operator Seq =
      cmp99OmegaSourcePhysicalOneStepSectionCCutFactor
        Seq r Cuts rho U hspacing ha := by
  apply ContinuousLinearMap.ext
  intro x
  rfl

end

end YangMills.RG
