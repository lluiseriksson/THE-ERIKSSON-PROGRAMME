/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceGeneratedCanonicalTerminalRestriction

/-!
# Physical realization of the canonical terminal restriction

The canonical iterated source towers end on the original physical source
regions.  This module identifies the recursively selected terminal map,
after transporting both Hilbert bundles to those regions, with literal
physical restriction.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator RealInnerProductSpace

noncomputable section

variable {d M N Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero N] [NeZero Nc]

/-- Transport through an equality is heterogeneously the identity. -/
theorem cmp99EqRec_heq_self {α : Sort*} (P : α → Sort*) {a b : α}
    (h : a = b) (x : P a) : HEq (h ▸ x) x := by
  cases h
  rfl

/-- Bundle transport preserves subtraction of rectangular maps. -/
theorem cmp99SourceTerminalCLMTransport_sub
    {E F E' F' : CMP99SourceWeightedTowerHilbertSpace}
    (hE : E = E') (hF : F = F')
    (C D : E.carrier →L[ℝ] F.carrier) :
    cmp99SourceTerminalCLMTransport hE hF (C - D) =
      cmp99SourceTerminalCLMTransport hE hF C -
        cmp99SourceTerminalCLMTransport hE hF D := by
  subst E'
  subst F'
  rfl

/-- Self-adjointness survives transport to a physical terminal bundle. -/
theorem cmp99SourceTerminalCLMTransport_adjoint_eq_self
    {E E' : CMP99SourceWeightedTowerHilbertSpace}
    (hE : E = E') (C : E.carrier →L[ℝ] E.carrier)
    (hC : C.adjoint = C) :
    (cmp99SourceTerminalCLMTransport hE hE C).adjoint =
      cmp99SourceTerminalCLMTransport hE hE C := by
  rw [← cmp99SourceTerminalCLMTransport_adjoint, hC]

/-- Terminal restrictions attached to heterogeneously equal nested chains
are themselves heterogeneously equal.  Quantifying the regions and chains
as variables makes dependent elimination stable; proof irrelevance removes
any dependence on how nestedness was constructed. -/
theorem CMP99SourceNestedRegionChains.terminalRestriction_heq_of_cast
    {depth : ℕ}
    {OmegaSmall OmegaLarge OmegaSmall' OmegaLarge' : ActiveGaugeRegion d N}
    (hOmegaSmall : OmegaSmall = OmegaSmall')
    (hOmegaLarge : OmegaLarge = OmegaLarge')
    {regionsSmall : CMP99SourceActiveRegionChain d M N OmegaSmall depth}
    {regionsLarge : CMP99SourceActiveRegionChain d M N OmegaLarge depth}
    {regionsSmall' : CMP99SourceActiveRegionChain d M N OmegaSmall' depth}
    {regionsLarge' : CMP99SourceActiveRegionChain d M N OmegaLarge' depth}
    (hregionsSmall : HEq regionsSmall regionsSmall')
    (hregionsLarge : HEq regionsLarge regionsLarge')
    (H : CMP99SourceNestedRegionChains d M regionsSmall regionsLarge)
    (H' : CMP99SourceNestedRegionChains d M regionsSmall' regionsLarge')
    (hd : 2 ≤ d) (hM : 2 ≤ M) (rho : SUNAdjointModel Nc)
    (spacing epsilon : ℝ) (background : GaugeConfig d N (SUN Nc))
    (chain : CMP99SourceUbarRadiusChain d M Nc depth epsilon)
    (fineSmall : ∀ e : ConcreteEdge d N,
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon) :
    HEq (H.terminalRestriction hd hM rho spacing epsilon background chain
          fineSmall)
      (H'.terminalRestriction hd hM rho spacing epsilon background chain
          fineSmall) := by
  subst OmegaSmall'
  subst OmegaLarge'
  have hs : regionsSmall = regionsSmall' := eq_of_heq hregionsSmall
  have hl : regionsLarge = regionsLarge' := eq_of_heq hregionsLarge
  subst regionsSmall'
  subst regionsLarge'
  have hH : H = H' := Subsingleton.elim _ _
  subst H'
  rfl

set_option maxRecDepth 6000 in
set_option synthInstance.maxHeartbeats 3000000 in
set_option maxHeartbeats 12000000 in
/-- The canonical iterated terminal restriction, transported to the two
original physical source Hilbert bundles, is literal physical restriction.
-/
theorem cmp99SourceIteratedLiftTerminalRestriction_transport_eq_physical
    {OmegaSmall OmegaLarge : ActiveGaugeRegion d N}
    (hsub : OmegaSmall.sites ⊆ OmegaLarge.sites)
    (hd : 2 ≤ d) (hM : 2 ≤ M) (rho : SUNAdjointModel Nc)
    (depth : ℕ) (spacing epsilon : ℝ)
    (background : GaugeConfig d
      (cmp99RegionalLatticeSize M N depth) (SUN Nc))
    (chain : CMP99SourceUbarRadiusChain d M Nc depth epsilon)
    (fineSmall : ∀ e : ConcreteEdge d
      (cmp99RegionalLatticeSize M N depth),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon) :
    let hsSmall := cmp99SourceIteratedLift_weightedQprimeTower_terminalSpace_eq
      hd hM rho OmegaSmall depth spacing epsilon background chain fineSmall
    let hsLarge := cmp99SourceIteratedLift_weightedQprimeTower_terminalSpace_eq
      hd hM rho OmegaLarge depth spacing epsilon background chain fineSmall
    cmp99SourceTerminalCLMTransport hsLarge hsSmall
        (cmp99SourceIteratedLiftTerminalRestriction hsub hd hM rho depth
          spacing epsilon background chain fineSmall) =
      cmp99NestedActiveRegionRestriction
        (g := SUNLieCoord Nc) OmegaSmall OmegaLarge := by
  induction depth generalizing spacing epsilon with
  | zero =>
      dsimp only
      rw [cmp99SourceIteratedLiftTerminalRestriction_zero]
      rfl
  | succ depth ih =>
      dsimp only
      let fineRegionSmall :=
        cmp99IteratedLiftActiveRegion (M := M) OmegaSmall (depth + 1)
      let fineRegionLarge :=
        cmp99IteratedLiftActiveRegion (M := M) OmegaLarge (depth + 1)
      have hSaturatedSmall : fineRegionSmall.BlockSaturated :=
        cmp99IteratedLiftActiveRegion_blockSaturated OmegaSmall depth
      have hSaturatedLarge : fineRegionLarge.BlockSaturated :=
        cmp99IteratedLiftActiveRegion_blockSaturated OmegaLarge depth
      have hFine : fineRegionSmall.sites ⊆ fineRegionLarge.sites :=
        cmp99IteratedLiftActiveRegion_sites_mono hsub (depth + 1)
      have hCoarseSmall : cmp99ActiveCoarseRegion (M := M)
          (N' := cmp99RegionalLatticeSize M N depth) fineRegionSmall =
          cmp99IteratedLiftActiveRegion (M := M) OmegaSmall depth := by
        simpa [fineRegionSmall] using
          cmp99ActiveCoarseRegion_iteratedLift_succ_eq
            (M := M) OmegaSmall depth
      have hCoarseLarge : cmp99ActiveCoarseRegion (M := M)
          (N' := cmp99RegionalLatticeSize M N depth) fineRegionLarge =
          cmp99IteratedLiftActiveRegion (M := M) OmegaLarge depth := by
        simpa [fineRegionLarge] using
          cmp99ActiveCoarseRegion_iteratedLift_succ_eq
            (M := M) OmegaLarge depth
      let canonicalSmall := cmp99SourceIteratedLiftActiveRegionChain
        (M := M) OmegaSmall depth
      let canonicalLarge := cmp99SourceIteratedLiftActiveRegionChain
        (M := M) OmegaLarge depth
      let tailSmall : CMP99SourceActiveRegionChain d M
          (cmp99RegionalLatticeSize M N depth)
          (cmp99ActiveCoarseRegion (M := M)
            (N' := cmp99RegionalLatticeSize M N depth) fineRegionSmall) depth :=
        hCoarseSmall.symm ▸ canonicalSmall
      let tailLarge : CMP99SourceActiveRegionChain d M
          (cmp99RegionalLatticeSize M N depth)
          (cmp99ActiveCoarseRegion (M := M)
            (N' := cmp99RegionalLatticeSize M N depth) fineRegionLarge) depth :=
        hCoarseLarge.symm ▸ canonicalLarge
      let HcanonicalDepth :=
        cmp99SourceIteratedLift_nestedRegionChains (M := M) hsub depth
      have hTail : CMP99SourceNestedRegionChains d M tailSmall tailLarge := by
        exact CMP99SourceNestedRegionChains.cast_regions
          hCoarseSmall.symm hCoarseLarge.symm HcanonicalDepth
      let builtSmall := CMP99SourceActiveRegionChain.step fineRegionSmall
        hSaturatedSmall tailSmall
      let builtLarge := CMP99SourceActiveRegionChain.step fineRegionLarge
        hSaturatedLarge tailLarge
      have hbSmall : builtSmall =
          cmp99SourceIteratedLiftActiveRegionChain (M := M) OmegaSmall
            (depth + 1) := by
        dsimp [builtSmall, cmp99SourceIteratedLiftActiveRegionChain,
          fineRegionSmall, tailSmall, canonicalSmall]
        congr 1
        apply eq_of_heq
        exact eqRec_heq_iff_heq.mpr (cast_heq _ _).symm
      have hbLarge : builtLarge =
          cmp99SourceIteratedLiftActiveRegionChain (M := M) OmegaLarge
            (depth + 1) := by
        dsimp [builtLarge, cmp99SourceIteratedLiftActiveRegionChain,
          fineRegionLarge, tailLarge, canonicalLarge]
        congr 1
        apply eq_of_heq
        exact eqRec_heq_iff_heq.mpr (cast_heq _ _).symm
      let Hstep := CMP99SourceNestedRegionChains.step fineRegionSmall
        fineRegionLarge hSaturatedSmall hSaturatedLarge hFine tailSmall
        tailLarge hTail
      let HcanonicalSucc :=
        cmp99SourceIteratedLift_nestedRegionChains (M := M) hsub (depth + 1)
      let ScaleSmall : CMP99SourceNormalizedRegionalScale fineRegionSmall
          background := CMP99SourceNormalizedRegionalScale.ofFineSmall hd hM
        fineRegionSmall background hSaturatedSmall epsilon
        chain.epsilon_nonneg chain.head_noWinding fineSmall
      have nextSmall : ∀ e : ConcreteEdge d
          (cmp99RegionalLatticeSize M N depth),
          ‖(ScaleSmall.toSourceScale.data.nextBackground e :
              Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤
            cmp99SourceUbarNextFineRadius d M epsilon := by
        intro e
        simpa [ScaleSmall, CMP99SourceNormalizedRegionalScale.ofFineSmall,
          CMP99SourceRegionalScale.ofFineSmall] using
          norm_cmp99SourceRegionalScaleDataOfFineSmall_nextBackground_sub_one_le
            hd hM fineRegionSmall background (cmp99SourceBlockAverageWeight M d)
            epsilon chain.epsilon_nonneg chain.head_noWinding
            chain.head_logSmall fineSmall e
      have hSuccStep : HEq
          (HcanonicalSucc.terminalRestriction hd hM rho spacing epsilon
            background chain fineSmall)
          (Hstep.terminalRestriction hd hM rho spacing epsilon background
            chain fineSmall) :=
        CMP99SourceNestedRegionChains.terminalRestriction_heq_of_cast
          rfl rfl hbSmall.symm.heq hbLarge.symm.heq HcanonicalSucc Hstep
          hd hM rho spacing epsilon background chain fineSmall
      have hStepTail :
          Hstep.terminalRestriction hd hM rho spacing epsilon background chain
              fineSmall =
            hTail.terminalRestriction hd hM rho ((M : ℝ) * spacing)
              (cmp99SourceUbarNextFineRadius d M epsilon)
              ScaleSmall.toSourceScale.data.nextBackground chain.tail
              nextSmall := by
        exact CMP99SourceNestedRegionChains.terminalRestriction_step
          fineRegionSmall fineRegionLarge hSaturatedSmall hSaturatedLarge hFine
          tailSmall tailLarge hTail hd hM rho spacing epsilon background chain
          fineSmall
      have hTailSmall : HEq tailSmall canonicalSmall := by
        dsimp [tailSmall]
        exact cmp99EqRec_heq_self
          (fun region => CMP99SourceActiveRegionChain d M
            (cmp99RegionalLatticeSize M N depth) region depth)
          hCoarseSmall.symm canonicalSmall
      have hTailLarge : HEq tailLarge canonicalLarge := by
        dsimp [tailLarge]
        exact cmp99EqRec_heq_self
          (fun region => CMP99SourceActiveRegionChain d M
            (cmp99RegionalLatticeSize M N depth) region depth)
          hCoarseLarge.symm canonicalLarge
      have hTailCanonical : HEq
          (hTail.terminalRestriction hd hM rho ((M : ℝ) * spacing)
            (cmp99SourceUbarNextFineRadius d M epsilon)
            ScaleSmall.toSourceScale.data.nextBackground chain.tail nextSmall)
          (HcanonicalDepth.terminalRestriction hd hM rho ((M : ℝ) * spacing)
            (cmp99SourceUbarNextFineRadius d M epsilon)
            ScaleSmall.toSourceScale.data.nextBackground chain.tail nextSmall) :=
        CMP99SourceNestedRegionChains.terminalRestriction_heq_of_cast
          hCoarseSmall hCoarseLarge hTailSmall hTailLarge
          hTail HcanonicalDepth hd hM rho ((M : ℝ) * spacing)
          (cmp99SourceUbarNextFineRadius d M epsilon)
          ScaleSmall.toSourceScale.data.nextBackground chain.tail nextSmall
      have hMaps : HEq
          (cmp99SourceIteratedLiftTerminalRestriction hsub hd hM rho
            (depth + 1) spacing epsilon background chain fineSmall)
          (cmp99SourceIteratedLiftTerminalRestriction hsub hd hM rho depth
            ((M : ℝ) * spacing) (cmp99SourceUbarNextFineRadius d M epsilon)
            ScaleSmall.toSourceScale.data.nextBackground chain.tail
            nextSmall) := by
        unfold cmp99SourceIteratedLiftTerminalRestriction
        exact hSuccStep.trans (hStepTail.heq.trans hTailCanonical)
      let hsSmallSucc :=
        cmp99SourceIteratedLift_weightedQprimeTower_terminalSpace_eq hd hM rho
          OmegaSmall (depth + 1) spacing epsilon background chain fineSmall
      let hsLargeSucc :=
        cmp99SourceIteratedLift_weightedQprimeTower_terminalSpace_eq hd hM rho
          OmegaLarge (depth + 1) spacing epsilon background chain fineSmall
      let hsSmallDepth :=
        cmp99SourceIteratedLift_weightedQprimeTower_terminalSpace_eq hd hM rho
          OmegaSmall depth ((M : ℝ) * spacing)
          (cmp99SourceUbarNextFineRadius d M epsilon)
          ScaleSmall.toSourceScale.data.nextBackground chain.tail nextSmall
      let hsLargeDepth :=
        cmp99SourceIteratedLift_weightedQprimeTower_terminalSpace_eq hd hM rho
          OmegaLarge depth ((M : ℝ) * spacing)
          (cmp99SourceUbarNextFineRadius d M epsilon)
          ScaleSmall.toSourceScale.data.nextBackground chain.tail nextSmall
      have htransport := cmp99SourceTerminalCLMTransport_eq_of_heq
        hsLargeSucc hsSmallSucc hsLargeDepth hsSmallDepth
        (cmp99SourceIteratedLiftTerminalRestriction hsub hd hM rho
          (depth + 1) spacing epsilon background chain fineSmall)
        (cmp99SourceIteratedLiftTerminalRestriction hsub hd hM rho depth
          ((M : ℝ) * spacing) (cmp99SourceUbarNextFineRadius d M epsilon)
          ScaleSmall.toSourceScale.data.nextBackground chain.tail nextSmall)
        hMaps
      exact htransport.trans
        (ih ((M : ℝ) * spacing)
          (cmp99SourceUbarNextFineRadius d M epsilon)
          ScaleSmall.toSourceScale.data.nextBackground chain.tail nextSmall)

end

end YangMills.RG
