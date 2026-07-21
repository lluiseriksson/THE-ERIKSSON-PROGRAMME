/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceGeneratedTerminalRestrictionUniqueness

/-!
# Recursive characterization of the CMP99 terminal restriction

Exact source coisometry makes the selected terminal restriction unique.
We use that uniqueness to expose its two source-faithful recursion laws:
at depth zero it is literal restriction, and across one generated scale it
is exactly the terminal restriction of the two coarse tails.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator RealInnerProductSpace

noncomputable section

variable {d M Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero Nc]

/-- At the terminal scale itself, the selected map is ordinary restriction
between the two literal active regions. -/
theorem CMP99SourceNestedRegionChains.terminalRestriction_stop
    {N : ℕ} [NeZero N]
    (OmegaSmall OmegaLarge : ActiveGaugeRegion d N)
    (hsub : OmegaSmall.sites ⊆ OmegaLarge.sites)
    (hd : 2 ≤ d) (hM : 2 ≤ M) (rho : SUNAdjointModel Nc)
    (spacing epsilon : ℝ) (background : GaugeConfig d N (SUN Nc))
    (chain : CMP99SourceUbarRadiusChain d M Nc 0 epsilon)
    (fineSmall : ∀ e : ConcreteEdge d N,
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon) :
    (CMP99SourceNestedRegionChains.stop (M := M)
        OmegaSmall OmegaLarge hsub).terminalRestriction hd hM rho spacing
          epsilon background chain fineSmall =
      cmp99NestedActiveRegionRestriction
        (g := SUNLieCoord Nc) OmegaSmall OmegaLarge := by
  let H := CMP99SourceNestedRegionChains.stop (M := M)
    OmegaSmall OmegaLarge hsub
  apply Eq.symm
  apply H.terminalRestriction_unique hd hM rho spacing epsilon background
    chain fineSmall
  change (ContinuousLinearMap.id ℝ _).comp
      (cmp99NestedActiveRegionRestriction OmegaSmall OmegaLarge) =
    (cmp99NestedActiveRegionRestriction OmegaSmall OmegaLarge).comp
      (ContinuousLinearMap.id ℝ _)
  rw [ContinuousLinearMap.id_comp, ContinuousLinearMap.comp_id]

/-- Across one generated scale, the selected terminal map is exactly the
selected terminal restriction of the two coarse tails. -/
theorem CMP99SourceNestedRegionChains.terminalRestriction_step
    {N depth : ℕ} [NeZero N]
    (OmegaSmall OmegaLarge : ActiveGaugeRegion d (M * N))
    (hSmall : OmegaSmall.BlockSaturated)
    (hLarge : OmegaLarge.BlockSaturated)
    (hsub : OmegaSmall.sites ⊆ OmegaLarge.sites)
    (tailSmall : CMP99SourceActiveRegionChain d M N
      (cmp99ActiveCoarseRegion (M := M) (N' := N) OmegaSmall) depth)
    (tailLarge : CMP99SourceActiveRegionChain d M N
      (cmp99ActiveCoarseRegion (M := M) (N' := N) OmegaLarge) depth)
    (tailNested : CMP99SourceNestedRegionChains d M tailSmall tailLarge)
    (hd : 2 ≤ d) (hM : 2 ≤ M) (rho : SUNAdjointModel Nc)
    (spacing epsilon : ℝ)
    (background : GaugeConfig d (M * N) (SUN Nc))
    (chain : CMP99SourceUbarRadiusChain d M Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge d (M * N),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon) :
    let ScaleSmall : CMP99SourceNormalizedRegionalScale OmegaSmall
        background :=
      CMP99SourceNormalizedRegionalScale.ofFineSmall hd hM OmegaSmall
        background hSmall epsilon chain.epsilon_nonneg
        chain.head_noWinding fineSmall
    let nextSmall : ∀ e : ConcreteEdge d N,
        ‖(ScaleSmall.toSourceScale.data.nextBackground e :
            Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤
          cmp99SourceUbarNextFineRadius d M epsilon := by
      intro e
      simpa [ScaleSmall, CMP99SourceNormalizedRegionalScale.ofFineSmall,
        CMP99SourceRegionalScale.ofFineSmall] using
        norm_cmp99SourceRegionalScaleDataOfFineSmall_nextBackground_sub_one_le
          hd hM OmegaSmall background (cmp99SourceBlockAverageWeight M d)
          epsilon chain.epsilon_nonneg chain.head_noWinding
          chain.head_logSmall fineSmall e
    let H := CMP99SourceNestedRegionChains.step OmegaSmall OmegaLarge
      hSmall hLarge hsub tailSmall tailLarge tailNested
    H.terminalRestriction hd hM rho spacing epsilon background chain
        fineSmall =
      tailNested.terminalRestriction hd hM rho ((M : ℝ) * spacing)
        (cmp99SourceUbarNextFineRadius d M epsilon)
        ScaleSmall.toSourceScale.data.nextBackground chain.tail nextSmall := by
  dsimp only
  let ScaleSmall : CMP99SourceNormalizedRegionalScale OmegaSmall background :=
    CMP99SourceNormalizedRegionalScale.ofFineSmall hd hM OmegaSmall
      background hSmall epsilon chain.epsilon_nonneg chain.head_noWinding
      fineSmall
  let ScaleLarge : CMP99SourceNormalizedRegionalScale OmegaLarge background :=
    CMP99SourceNormalizedRegionalScale.ofFineSmall hd hM OmegaLarge
      background hLarge epsilon chain.epsilon_nonneg chain.head_noWinding
      fineSmall
  have nextSmall : ∀ e : ConcreteEdge d N,
      ‖(ScaleSmall.toSourceScale.data.nextBackground e :
          Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤
        cmp99SourceUbarNextFineRadius d M epsilon := by
    intro e
    simpa [ScaleSmall, CMP99SourceNormalizedRegionalScale.ofFineSmall,
      CMP99SourceRegionalScale.ofFineSmall] using
      norm_cmp99SourceRegionalScaleDataOfFineSmall_nextBackground_sub_one_le
        hd hM OmegaSmall background (cmp99SourceBlockAverageWeight M d)
        epsilon chain.epsilon_nonneg chain.head_noWinding chain.head_logSmall
        fineSmall e
  let H := CMP99SourceNestedRegionChains.step OmegaSmall OmegaLarge
    hSmall hLarge hsub tailSmall tailLarge tailNested
  let Rtail := tailNested.terminalRestriction hd hM rho
    ((M : ℝ) * spacing) (cmp99SourceUbarNextFineRadius d M epsilon)
    ScaleSmall.toSourceScale.data.nextBackground chain.tail nextSmall
  apply Eq.symm
  apply H.terminalRestriction_unique hd hM rho spacing epsilon background
    chain fineSmall
  let Qsmall := cmp99SourceTransportedBlockAverageCLM OmegaSmall
    (cmp99SourceWeightedPhysicalTransport rho background)
  let Qlarge := cmp99SourceTransportedBlockAverageCLM OmegaLarge
    (cmp99SourceWeightedPhysicalTransport rho background)
  let Rfine := cmp99NestedActiveRegionRestriction
    (g := SUNLieCoord Nc) OmegaSmall OmegaLarge
  let Rcoarse := cmp99NestedActiveRegionRestriction
    (g := SUNLieCoord Nc)
    (cmp99ActiveCoarseRegion (M := M) (N' := N) OmegaSmall)
    (cmp99ActiveCoarseRegion (M := M) (N' := N) OmegaLarge)
  have hQhead : Qsmall.comp Rfine = Rcoarse.comp Qlarge :=
    cmp99SourceTransportedBlockAverage_nested_transition
      OmegaSmall OmegaLarge hsub
      (cmp99SourceWeightedPhysicalTransport rho background)
  have hQtail :
      (tailSmall.weightedQprimeTower hd hM rho ((M : ℝ) * spacing)
        (cmp99SourceUbarNextFineRadius d M epsilon)
        ScaleSmall.toSourceScale.data.nextBackground chain.tail
        nextSmall).Qprime.comp Rcoarse =
      Rtail.comp
        (tailLarge.weightedQprimeTower hd hM rho ((M : ℝ) * spacing)
          (cmp99SourceUbarNextFineRadius d M epsilon)
          ScaleLarge.toSourceScale.data.nextBackground chain.tail
          nextSmall).Qprime := by
    simpa [Rcoarse, Rtail, ScaleSmall, ScaleLarge,
      CMP99SourceNormalizedRegionalScale.ofFineSmall,
      CMP99SourceRegionalScale.ofFineSmall] using
      tailNested.Qprime_comp_restriction hd hM rho ((M : ℝ) * spacing)
        (cmp99SourceUbarNextFineRadius d M epsilon)
        ScaleSmall.toSourceScale.data.nextBackground chain.tail nextSmall
  change
      ((tailSmall.weightedQprimeTower hd hM rho ((M : ℝ) * spacing)
        (cmp99SourceUbarNextFineRadius d M epsilon)
        ScaleSmall.toSourceScale.data.nextBackground chain.tail
        nextSmall).Qprime.comp Qsmall).comp Rfine =
    Rtail.comp
      ((tailLarge.weightedQprimeTower hd hM rho ((M : ℝ) * spacing)
        (cmp99SourceUbarNextFineRadius d M epsilon)
        ScaleLarge.toSourceScale.data.nextBackground chain.tail
        nextSmall).Qprime.comp Qlarge)
  calc
    _ = (tailSmall.weightedQprimeTower hd hM rho ((M : ℝ) * spacing)
          (cmp99SourceUbarNextFineRadius d M epsilon)
          ScaleSmall.toSourceScale.data.nextBackground chain.tail
          nextSmall).Qprime.comp (Qsmall.comp Rfine) := by
        rw [ContinuousLinearMap.comp_assoc]
    _ = (tailSmall.weightedQprimeTower hd hM rho ((M : ℝ) * spacing)
          (cmp99SourceUbarNextFineRadius d M epsilon)
          ScaleSmall.toSourceScale.data.nextBackground chain.tail
          nextSmall).Qprime.comp (Rcoarse.comp Qlarge) := by rw [hQhead]
    _ = ((tailSmall.weightedQprimeTower hd hM rho ((M : ℝ) * spacing)
          (cmp99SourceUbarNextFineRadius d M epsilon)
          ScaleSmall.toSourceScale.data.nextBackground chain.tail
          nextSmall).Qprime.comp Rcoarse).comp Qlarge := by
        rw [ContinuousLinearMap.comp_assoc]
    _ = (Rtail.comp
          (tailLarge.weightedQprimeTower hd hM rho ((M : ℝ) * spacing)
            (cmp99SourceUbarNextFineRadius d M epsilon)
            ScaleLarge.toSourceScale.data.nextBackground chain.tail
            nextSmall).Qprime).comp Qlarge := by rw [hQtail]
    _ = _ := by rfl

end

end YangMills.RG
