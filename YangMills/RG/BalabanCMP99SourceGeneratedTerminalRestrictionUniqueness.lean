/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceGeneratedQprimeTransition

/-!
# Uniqueness of the generated terminal restriction

The terminal map used by the generated CMP99 tower was selected from a
joint existence theorem.  Exact source coisometry makes that map unique:
the `Q'` intertwining law alone determines it.  This removes any semantic
ambiguity from the noncomputable choice and permits a later literal
restriction producer to be identified with the existing public map.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator RealInnerProductSpace

noncomputable section

variable {d M N Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero Nc]

/-- A terminal operator satisfying the physical `Q'` intertwining law is
equal to the terminal restriction selected by the joint construction. -/
theorem CMP99SourceNestedRegionChains.terminalRestriction_unique
    {depth : ℕ} [NeZero N]
    {OmegaSmall OmegaLarge : ActiveGaugeRegion d N}
    {regionsSmall : CMP99SourceActiveRegionChain d M N OmegaSmall depth}
    {regionsLarge : CMP99SourceActiveRegionChain d M N OmegaLarge depth}
    (H : CMP99SourceNestedRegionChains d M regionsSmall regionsLarge)
    (hd : 2 ≤ d) (hM : 2 ≤ M) (rho : SUNAdjointModel Nc)
    (spacing epsilon : ℝ) (background : GaugeConfig d N (SUN Nc))
    (chain : CMP99SourceUbarRadiusChain d M Nc depth epsilon)
    (fineSmall : ∀ e : ConcreteEdge d N,
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon) :
    let Tsmall := regionsSmall.weightedQprimeTower hd hM rho spacing epsilon
      background chain fineSmall
    let Tlarge := regionsLarge.weightedQprimeTower hd hM rho spacing epsilon
      background chain fineSmall
    let Rfine := cmp99NestedActiveRegionRestriction
      (g := SUNLieCoord Nc) OmegaSmall OmegaLarge
    ∀ (R : Tlarge.TerminalSpace.carrier →L[ℝ]
        Tsmall.TerminalSpace.carrier),
      Tsmall.Qprime.comp Rfine = R.comp Tlarge.Qprime →
      R = H.terminalRestriction hd hM rho spacing epsilon background chain
        fineSmall := by
  dsimp only
  intro R hR
  let Tsmall := regionsSmall.weightedQprimeTower hd hM rho spacing epsilon
    background chain fineSmall
  let Tlarge := regionsLarge.weightedQprimeTower hd hM rho spacing epsilon
    background chain fineSmall
  let Rfine := cmp99NestedActiveRegionRestriction
    (g := SUNLieCoord Nc) OmegaSmall OmegaLarge
  let Rchosen := H.terminalRestriction hd hM rho spacing epsilon background
    chain fineSmall
  have hchosen : Tsmall.Qprime.comp Rfine = Rchosen.comp Tlarge.Qprime :=
    H.Qprime_comp_restriction hd hM rho spacing epsilon background chain
      fineSmall
  have hcois : Tlarge.Qprime.comp Tlarge.weightedAdjoint =
      ContinuousLinearMap.id ℝ Tlarge.TerminalSpace.carrier :=
    regionsLarge.weightedQprimeTower_comp_weightedAdjoint hd hM rho spacing
      epsilon background chain fineSmall
  change R = Rchosen
  calc
    R = R.comp (ContinuousLinearMap.id ℝ Tlarge.TerminalSpace.carrier) := by
      rw [ContinuousLinearMap.comp_id]
    _ = R.comp (Tlarge.Qprime.comp Tlarge.weightedAdjoint) := by rw [hcois]
    _ = (R.comp Tlarge.Qprime).comp Tlarge.weightedAdjoint := by
      rw [ContinuousLinearMap.comp_assoc]
    _ = (Tsmall.Qprime.comp Rfine).comp Tlarge.weightedAdjoint := by
      rw [hR]
    _ = (Rchosen.comp Tlarge.Qprime).comp Tlarge.weightedAdjoint := by
      rw [hchosen]
    _ = Rchosen.comp (Tlarge.Qprime.comp Tlarge.weightedAdjoint) := by
      rw [ContinuousLinearMap.comp_assoc]
    _ = Rchosen.comp (ContinuousLinearMap.id ℝ
        Tlarge.TerminalSpace.carrier) := by rw [hcois]
    _ = Rchosen := by rw [ContinuousLinearMap.comp_id]

/-- The selected restriction has an explicit coisometric formula. -/
theorem CMP99SourceNestedRegionChains.terminalRestriction_eq_Qprime_comp
    {depth : ℕ} [NeZero N]
    {OmegaSmall OmegaLarge : ActiveGaugeRegion d N}
    {regionsSmall : CMP99SourceActiveRegionChain d M N OmegaSmall depth}
    {regionsLarge : CMP99SourceActiveRegionChain d M N OmegaLarge depth}
    (H : CMP99SourceNestedRegionChains d M regionsSmall regionsLarge)
    (hd : 2 ≤ d) (hM : 2 ≤ M) (rho : SUNAdjointModel Nc)
    (spacing epsilon : ℝ) (background : GaugeConfig d N (SUN Nc))
    (chain : CMP99SourceUbarRadiusChain d M Nc depth epsilon)
    (fineSmall : ∀ e : ConcreteEdge d N,
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon) :
    let Tsmall := regionsSmall.weightedQprimeTower hd hM rho spacing epsilon
      background chain fineSmall
    let Tlarge := regionsLarge.weightedQprimeTower hd hM rho spacing epsilon
      background chain fineSmall
    let Rfine := cmp99NestedActiveRegionRestriction
      (g := SUNLieCoord Nc) OmegaSmall OmegaLarge
    H.terminalRestriction hd hM rho spacing epsilon background chain
        fineSmall =
      Tsmall.Qprime.comp (Rfine.comp Tlarge.weightedAdjoint) := by
  dsimp only
  have htransition := H.Qprime_comp_restriction hd hM rho spacing epsilon
    background chain fineSmall
  have hcois := regionsLarge.weightedQprimeTower_comp_weightedAdjoint hd hM
    rho spacing epsilon background chain fineSmall
  let Rchosen := H.terminalRestriction hd hM rho spacing epsilon background
    chain fineSmall
  calc
    Rchosen = Rchosen.comp (ContinuousLinearMap.id ℝ
        (regionsLarge.weightedQprimeTower hd hM rho spacing epsilon background
          chain fineSmall).TerminalSpace.carrier) := by
      rw [ContinuousLinearMap.comp_id]
    _ = Rchosen.comp
        ((regionsLarge.weightedQprimeTower hd hM rho spacing epsilon background
          chain fineSmall).Qprime.comp
        (regionsLarge.weightedQprimeTower hd hM rho spacing epsilon background
          chain fineSmall).weightedAdjoint) := by rw [hcois]
    _ = (Rchosen.comp
        (regionsLarge.weightedQprimeTower hd hM rho spacing epsilon background
          chain fineSmall).Qprime).comp
        (regionsLarge.weightedQprimeTower hd hM rho spacing epsilon background
          chain fineSmall).weightedAdjoint := by
      rw [ContinuousLinearMap.comp_assoc]
    _ = ((regionsSmall.weightedQprimeTower hd hM rho spacing epsilon background
          chain fineSmall).Qprime.comp
        (cmp99NestedActiveRegionRestriction
          (g := SUNLieCoord Nc) OmegaSmall OmegaLarge)).comp
        (regionsLarge.weightedQprimeTower hd hM rho spacing epsilon background
          chain fineSmall).weightedAdjoint := by rw [htransition]
    _ = (regionsSmall.weightedQprimeTower hd hM rho spacing epsilon background
          chain fineSmall).Qprime.comp
        ((cmp99NestedActiveRegionRestriction
          (g := SUNLieCoord Nc) OmegaSmall OmegaLarge).comp
        (regionsLarge.weightedQprimeTower hd hM rho spacing epsilon background
          chain fineSmall).weightedAdjoint) := by
      rw [ContinuousLinearMap.comp_assoc]

end

end YangMills.RG
