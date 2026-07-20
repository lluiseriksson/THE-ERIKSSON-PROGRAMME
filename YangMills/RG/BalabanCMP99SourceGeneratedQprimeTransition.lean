/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceGeneratedMassTransition

/-!
# Exact transition of the generated CMP99 averaging tower

The generated Green comparison changes the fine regional carrier.  To pass
from it to the coarse covariance one also needs the induced restriction on
the terminal carrier of the complete `Q'` tower.  This file constructs that
restriction recursively from the same nested physical region chains and
proves the exact intertwining laws for `Q'` and its source-weighted adjoint.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator RealInnerProductSpace

noncomputable section

variable {d M N Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero Nc]

/-- Restriction between arbitrary nested active regions is contractive in
the counting Hilbert norm. -/
theorem norm_cmp99NestedActiveRegionRestriction_le_one
    {N : ℕ} [NeZero N]
    {OmegaSmall OmegaLarge : ActiveGaugeRegion d N}
    (hsub : OmegaSmall.sites ⊆ OmegaLarge.sites) :
    ‖cmp99NestedActiveRegionRestriction
      (g := SUNLieCoord Nc) OmegaSmall OmegaLarge‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro phi
  have hsq :
      ‖cmp99NestedActiveRegionRestriction
          (g := SUNLieCoord Nc) OmegaSmall OmegaLarge phi‖ ^ 2 ≤
        ‖phi‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
    let f : FinBox d N → ℝ := fun x =>
      ‖extendZeroZeroCLM OmegaLarge phi x‖ ^ 2
    calc
      ∑ x : ActiveGaugeRegion.Site OmegaSmall,
          ‖cmp99NestedActiveRegionRestriction
            (g := SUNLieCoord Nc) OmegaSmall OmegaLarge phi x‖ ^ 2 =
        ∑ x ∈ OmegaSmall.sites, f x := by
          rw [Finset.sum_subtype OmegaSmall.sites (fun _ => Iff.rfl) f]
          apply Finset.sum_congr rfl
          intro x _hx
          rfl
      _ ≤ ∑ x ∈ OmegaLarge.sites, f x :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub
          (fun x _ _ => sq_nonneg ‖extendZeroZeroCLM OmegaLarge phi x‖)
      _ = ∑ x : ActiveGaugeRegion.Site OmegaLarge, ‖phi x‖ ^ 2 := by
        rw [Finset.sum_subtype OmegaLarge.sites (fun _ => Iff.rfl) f]
        apply Finset.sum_congr rfl
        intro x _hx
        simp [f, extendZeroZeroCLM, x.2]
  nlinarith [norm_nonneg
    (cmp99NestedActiveRegionRestriction
      (g := SUNLieCoord Nc) OmegaSmall OmegaLarge phi), norm_nonneg phi]

/-- Source-weighted one-step synthesis commutes with restriction between
arbitrary nested complete-block regions. -/
theorem cmp99SourceTransportedBlockWeightedAdjoint_nested_transition
    {N : ℕ} [NeZero N]
    (OmegaSmall OmegaLarge : ActiveGaugeRegion d (M * N))
    (hSmall : OmegaSmall.BlockSaturated)
    (hLarge : OmegaLarge.BlockSaturated)
    (hsub : OmegaSmall.sites ⊆ OmegaLarge.sites)
    (transport : FinBox d N → FinBox d (M * N) →
      (SUNLieCoord Nc ≃ₗᵢ[ℝ] SUNLieCoord Nc)) :
    (cmp99NestedActiveRegionRestriction OmegaSmall OmegaLarge).comp
        (cmp99SourceTransportedBlockWeightedAdjointCLM
          OmegaLarge hLarge transport) =
      (cmp99SourceTransportedBlockWeightedAdjointCLM
        OmegaSmall hSmall transport).comp
        (cmp99NestedActiveRegionRestriction
          (cmp99ActiveCoarseRegion (M := M) (N' := N) OmegaSmall)
          (cmp99ActiveCoarseRegion (M := M) (N' := N) OmegaLarge)) := by
  have hadj := cmp99SourceTransportedBlockAverage_adjoint_nested_transition
    OmegaSmall OmegaLarge hSmall hLarge hsub transport
  rw [cmp99SourceTransportedBlockWeightedAdjointCLM_eq_smul_adjoint,
    cmp99SourceTransportedBlockWeightedAdjointCLM_eq_smul_adjoint]
  apply ContinuousLinearMap.ext
  intro eta
  have heta := congrArg (fun T => T eta) hadj
  simpa only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smul_apply, map_smul] using
      congrArg (fun z => (M : ℝ) ^ d • z) heta

/-- Two nested generated towers admit a terminal restriction which
simultaneously intertwines `Q'` and its source-weighted adjoint.  The two
laws are constructed in the same induction, so no unrelated terminal map
can enter either identity. -/
theorem CMP99SourceNestedRegionChains.exists_terminalRestriction_intertwining
    {N depth : ℕ} {OmegaSmall OmegaLarge : ActiveGaugeRegion d N}
    {regionsSmall : CMP99SourceActiveRegionChain d M N OmegaSmall depth}
    {regionsLarge : CMP99SourceActiveRegionChain d M N OmegaLarge depth}
    (H : CMP99SourceNestedRegionChains d M regionsSmall regionsLarge)
    (hd : 2 ≤ d) (hM : 2 ≤ M) (rho : SUNAdjointModel Nc) :
    letI : NeZero N := regionsSmall.neZero
    ∀ (spacing epsilon : ℝ) (background : GaugeConfig d N (SUN Nc))
      (chain : CMP99SourceUbarRadiusChain d M Nc depth epsilon)
      (fineSmall : ∀ e : ConcreteEdge d N,
        ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon),
      let Tsmall := regionsSmall.weightedQprimeTower hd hM rho spacing epsilon
        background chain fineSmall
      let Tlarge := regionsLarge.weightedQprimeTower hd hM rho spacing epsilon
        background chain fineSmall
      let Rfine := cmp99NestedActiveRegionRestriction
        (g := SUNLieCoord Nc) OmegaSmall OmegaLarge
      ∃ Rterminal : Tlarge.TerminalSpace.carrier →L[ℝ]
          Tsmall.TerminalSpace.carrier,
        Tsmall.Qprime.comp Rfine = Rterminal.comp Tlarge.Qprime ∧
        Rfine.comp Tlarge.weightedAdjoint =
          Tsmall.weightedAdjoint.comp Rterminal ∧
        ‖Rterminal‖ ≤ 1 := by
  letI : NeZero N := regionsSmall.neZero
  induction H with
  | stop OmegaSmall OmegaLarge hsub =>
      intro spacing epsilon background chain fineSmall
      let R := cmp99NestedActiveRegionRestriction
        (g := SUNLieCoord Nc) OmegaSmall OmegaLarge
      refine ⟨R, ?_, ?_, norm_cmp99NestedActiveRegionRestriction_le_one hsub⟩
      · change (ContinuousLinearMap.id ℝ _).comp R =
          R.comp (ContinuousLinearMap.id ℝ _)
        rw [ContinuousLinearMap.id_comp, ContinuousLinearMap.comp_id]
      · change R.comp (ContinuousLinearMap.id ℝ _) =
          (ContinuousLinearMap.id ℝ _).comp R
        rw [ContinuousLinearMap.comp_id, ContinuousLinearMap.id_comp]
  | @step N depth _ OmegaSmall OmegaLarge hSmall hLarge hsub
      tailSmall tailLarge tailNested ih =>
      intro spacing epsilon background chain fineSmall
      let ScaleSmall : CMP99SourceNormalizedRegionalScale OmegaSmall
          background :=
        CMP99SourceNormalizedRegionalScale.ofFineSmall hd hM OmegaSmall
          background hSmall epsilon chain.epsilon_nonneg
          chain.head_noWinding fineSmall
      let ScaleLarge : CMP99SourceNormalizedRegionalScale OmegaLarge
          background :=
        CMP99SourceNormalizedRegionalScale.ofFineSmall hd hM OmegaLarge
          background hLarge epsilon chain.epsilon_nonneg
          chain.head_noWinding fineSmall
      have nextSmall : ∀ e : ConcreteEdge d N,
          ‖(ScaleSmall.toSourceScale.data.nextBackground e :
              Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤
            cmp99SourceUbarNextFineRadius d M epsilon := by
        intro e
        simpa [ScaleSmall, CMP99SourceNormalizedRegionalScale.ofFineSmall,
          CMP99SourceRegionalScale.ofFineSmall] using
          norm_cmp99SourceRegionalScaleDataOfFineSmall_nextBackground_sub_one_le
            hd hM OmegaSmall background
            (cmp99SourceBlockAverageWeight M d) epsilon
            chain.epsilon_nonneg chain.head_noWinding chain.head_logSmall
            fineSmall e
      have hTail := ih ((M : ℝ) * spacing)
          (cmp99SourceUbarNextFineRadius d M epsilon)
          ScaleSmall.toSourceScale.data.nextBackground chain.tail nextSmall
      obtain ⟨Rterminal, hQtail, hStail, hRterminal⟩ := hTail
      let Qsmall := cmp99SourceTransportedBlockAverageCLM OmegaSmall
        (cmp99SourceWeightedPhysicalTransport rho background)
      let Qlarge := cmp99SourceTransportedBlockAverageCLM OmegaLarge
        (cmp99SourceWeightedPhysicalTransport rho background)
      let Ssmall := cmp99SourceTransportedBlockWeightedAdjointCLM
        OmegaSmall hSmall (cmp99SourceWeightedPhysicalTransport rho background)
      let Slarge := cmp99SourceTransportedBlockWeightedAdjointCLM
        OmegaLarge hLarge (cmp99SourceWeightedPhysicalTransport rho background)
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
      have hShead : Rfine.comp Slarge = Ssmall.comp Rcoarse :=
        cmp99SourceTransportedBlockWeightedAdjoint_nested_transition
          OmegaSmall OmegaLarge hSmall hLarge hsub
          (cmp99SourceWeightedPhysicalTransport rho background)
      have hQtail' :
          (tailSmall.weightedQprimeTower hd hM rho ((M : ℝ) * spacing)
            (cmp99SourceUbarNextFineRadius d M epsilon)
            ScaleSmall.toSourceScale.data.nextBackground chain.tail
            nextSmall).Qprime.comp Rcoarse =
          Rterminal.comp
            (tailLarge.weightedQprimeTower hd hM rho ((M : ℝ) * spacing)
              (cmp99SourceUbarNextFineRadius d M epsilon)
              ScaleLarge.toSourceScale.data.nextBackground chain.tail
              nextSmall).Qprime := by
        simpa [Rcoarse, ScaleSmall, ScaleLarge,
          CMP99SourceNormalizedRegionalScale.ofFineSmall,
          CMP99SourceRegionalScale.ofFineSmall] using hQtail
      have hStail' : Rcoarse.comp
          (tailLarge.weightedQprimeTower hd hM rho ((M : ℝ) * spacing)
            (cmp99SourceUbarNextFineRadius d M epsilon)
            ScaleLarge.toSourceScale.data.nextBackground chain.tail
            nextSmall).weightedAdjoint =
          (tailSmall.weightedQprimeTower hd hM rho ((M : ℝ) * spacing)
            (cmp99SourceUbarNextFineRadius d M epsilon)
            ScaleSmall.toSourceScale.data.nextBackground chain.tail
            nextSmall).weightedAdjoint.comp Rterminal := by
        simpa [Rcoarse, ScaleSmall, ScaleLarge,
          CMP99SourceNormalizedRegionalScale.ofFineSmall,
          CMP99SourceRegionalScale.ofFineSmall] using hStail
      refine ⟨Rterminal, ?_, ?_, hRterminal⟩
      · change
          ((tailSmall.weightedQprimeTower hd hM rho ((M : ℝ) * spacing)
            (cmp99SourceUbarNextFineRadius d M epsilon)
            ScaleSmall.toSourceScale.data.nextBackground chain.tail
            nextSmall).Qprime.comp Qsmall).comp Rfine =
          Rterminal.comp
            ((tailLarge.weightedQprimeTower hd hM rho ((M : ℝ) * spacing)
              (cmp99SourceUbarNextFineRadius d M epsilon)
              ScaleLarge.toSourceScale.data.nextBackground chain.tail
              nextSmall).Qprime.comp Qlarge)
        calc
          _ = (tailSmall.weightedQprimeTower hd hM rho
                ((M : ℝ) * spacing)
                (cmp99SourceUbarNextFineRadius d M epsilon)
                ScaleSmall.toSourceScale.data.nextBackground chain.tail
                nextSmall).Qprime.comp (Qsmall.comp Rfine) := by
              rw [ContinuousLinearMap.comp_assoc]
          _ = (tailSmall.weightedQprimeTower hd hM rho
                ((M : ℝ) * spacing)
                (cmp99SourceUbarNextFineRadius d M epsilon)
                ScaleSmall.toSourceScale.data.nextBackground chain.tail
                nextSmall).Qprime.comp (Rcoarse.comp Qlarge) := by rw [hQhead]
          _ = ((tailSmall.weightedQprimeTower hd hM rho
                ((M : ℝ) * spacing)
                (cmp99SourceUbarNextFineRadius d M epsilon)
                ScaleSmall.toSourceScale.data.nextBackground chain.tail
                nextSmall).Qprime.comp Rcoarse).comp Qlarge := by
              rw [ContinuousLinearMap.comp_assoc]
          _ = (Rterminal.comp
                (tailLarge.weightedQprimeTower hd hM rho
                  ((M : ℝ) * spacing)
                  (cmp99SourceUbarNextFineRadius d M epsilon)
                  ScaleLarge.toSourceScale.data.nextBackground chain.tail
                  nextSmall).Qprime).comp Qlarge := by rw [hQtail']
          _ = _ := by rfl
      · change Rfine.comp
          (Slarge.comp
            (tailLarge.weightedQprimeTower hd hM rho ((M : ℝ) * spacing)
              (cmp99SourceUbarNextFineRadius d M epsilon)
              ScaleLarge.toSourceScale.data.nextBackground chain.tail
              nextSmall).weightedAdjoint) =
          Ssmall.comp
            ((tailSmall.weightedQprimeTower hd hM rho ((M : ℝ) * spacing)
              (cmp99SourceUbarNextFineRadius d M epsilon)
              ScaleSmall.toSourceScale.data.nextBackground chain.tail
              nextSmall).weightedAdjoint.comp Rterminal)
        calc
          _ = (Rfine.comp Slarge).comp
                (tailLarge.weightedQprimeTower hd hM rho
                  ((M : ℝ) * spacing)
                  (cmp99SourceUbarNextFineRadius d M epsilon)
                  ScaleLarge.toSourceScale.data.nextBackground chain.tail
                  nextSmall).weightedAdjoint := by
              rw [ContinuousLinearMap.comp_assoc]
          _ = (Ssmall.comp Rcoarse).comp
                (tailLarge.weightedQprimeTower hd hM rho
                  ((M : ℝ) * spacing)
                  (cmp99SourceUbarNextFineRadius d M epsilon)
                  ScaleLarge.toSourceScale.data.nextBackground chain.tail
                  nextSmall).weightedAdjoint := by rw [hShead]
          _ = Ssmall.comp (Rcoarse.comp
                (tailLarge.weightedQprimeTower hd hM rho
                  ((M : ℝ) * spacing)
                  (cmp99SourceUbarNextFineRadius d M epsilon)
                  ScaleLarge.toSourceScale.data.nextBackground chain.tail
                  nextSmall).weightedAdjoint) := by
              rw [ContinuousLinearMap.comp_assoc]
          _ = Ssmall.comp
                ((tailSmall.weightedQprimeTower hd hM rho
                  ((M : ℝ) * spacing)
                  (cmp99SourceUbarNextFineRadius d M epsilon)
                  ScaleSmall.toSourceScale.data.nextBackground chain.tail
                  nextSmall).weightedAdjoint.comp Rterminal) := by
              rw [hStail']
              rfl

/-- Canonical terminal restriction selected from the joint physical
construction above. -/
noncomputable def CMP99SourceNestedRegionChains.terminalRestriction
    {N depth : ℕ} [NeZero N]
    {OmegaSmall OmegaLarge : ActiveGaugeRegion d N}
    {regionsSmall : CMP99SourceActiveRegionChain d M N OmegaSmall depth}
    {regionsLarge : CMP99SourceActiveRegionChain d M N OmegaLarge depth}
    (H : CMP99SourceNestedRegionChains d M regionsSmall regionsLarge)
    (hd : 2 ≤ d) (hM : 2 ≤ M) (rho : SUNAdjointModel Nc)
    (spacing epsilon : ℝ) (background : GaugeConfig d N (SUN Nc))
    (chain : CMP99SourceUbarRadiusChain d M Nc depth epsilon)
    (fineSmall : ∀ e : ConcreteEdge d N,
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon) :
    letI : NeZero N := regionsSmall.neZero
    let Tsmall := regionsSmall.weightedQprimeTower hd hM rho spacing epsilon
      background chain fineSmall
    let Tlarge := regionsLarge.weightedQprimeTower hd hM rho spacing epsilon
      background chain fineSmall
    Tlarge.TerminalSpace.carrier →L[ℝ] Tsmall.TerminalSpace.carrier := by
  letI : NeZero N := regionsSmall.neZero
  exact Classical.choose
    (H.exists_terminalRestriction_intertwining hd hM rho spacing epsilon
      background chain fineSmall)

/-- The selected terminal restriction intertwines the complete generated
`Q'` towers. -/
theorem CMP99SourceNestedRegionChains.Qprime_comp_restriction
    {N depth : ℕ} [NeZero N]
    {OmegaSmall OmegaLarge : ActiveGaugeRegion d N}
    {regionsSmall : CMP99SourceActiveRegionChain d M N OmegaSmall depth}
    {regionsLarge : CMP99SourceActiveRegionChain d M N OmegaLarge depth}
    (H : CMP99SourceNestedRegionChains d M regionsSmall regionsLarge)
    (hd : 2 ≤ d) (hM : 2 ≤ M) (rho : SUNAdjointModel Nc)
    (spacing epsilon : ℝ) (background : GaugeConfig d N (SUN Nc))
    (chain : CMP99SourceUbarRadiusChain d M Nc depth epsilon)
    (fineSmall : ∀ e : ConcreteEdge d N,
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon) :
    letI : NeZero N := regionsSmall.neZero
    let Tsmall := regionsSmall.weightedQprimeTower hd hM rho spacing epsilon
      background chain fineSmall
    let Tlarge := regionsLarge.weightedQprimeTower hd hM rho spacing epsilon
      background chain fineSmall
    let Rfine := cmp99NestedActiveRegionRestriction
      (g := SUNLieCoord Nc) OmegaSmall OmegaLarge
    Tsmall.Qprime.comp Rfine =
      (H.terminalRestriction hd hM rho spacing epsilon background chain
        fineSmall).comp Tlarge.Qprime := by
  letI : NeZero N := regionsSmall.neZero
  exact (Classical.choose_spec
    (H.exists_terminalRestriction_intertwining hd hM rho spacing epsilon
      background chain fineSmall)).1

/-- The same selected terminal restriction intertwines the complete
source-weighted adjoints. -/
theorem CMP99SourceNestedRegionChains.restriction_comp_weightedAdjoint
    {N depth : ℕ} [NeZero N]
    {OmegaSmall OmegaLarge : ActiveGaugeRegion d N}
    {regionsSmall : CMP99SourceActiveRegionChain d M N OmegaSmall depth}
    {regionsLarge : CMP99SourceActiveRegionChain d M N OmegaLarge depth}
    (H : CMP99SourceNestedRegionChains d M regionsSmall regionsLarge)
    (hd : 2 ≤ d) (hM : 2 ≤ M) (rho : SUNAdjointModel Nc)
    (spacing epsilon : ℝ) (background : GaugeConfig d N (SUN Nc))
    (chain : CMP99SourceUbarRadiusChain d M Nc depth epsilon)
    (fineSmall : ∀ e : ConcreteEdge d N,
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon) :
    letI : NeZero N := regionsSmall.neZero
    let Tsmall := regionsSmall.weightedQprimeTower hd hM rho spacing epsilon
      background chain fineSmall
    let Tlarge := regionsLarge.weightedQprimeTower hd hM rho spacing epsilon
      background chain fineSmall
    let Rfine := cmp99NestedActiveRegionRestriction
      (g := SUNLieCoord Nc) OmegaSmall OmegaLarge
    Rfine.comp Tlarge.weightedAdjoint = Tsmall.weightedAdjoint.comp
      (H.terminalRestriction hd hM rho spacing epsilon background chain
        fineSmall) := by
  letI : NeZero N := regionsSmall.neZero
  exact (Classical.choose_spec
    (H.exists_terminalRestriction_intertwining hd hM rho spacing epsilon
      background chain fineSmall)).2.1

/-- The terminal restriction selected by the joint physical construction is
contractive; the quantitative property is retained by the same choice as the
two intertwining laws. -/
theorem CMP99SourceNestedRegionChains.norm_terminalRestriction_le_one
    {N depth : ℕ} [NeZero N]
    {OmegaSmall OmegaLarge : ActiveGaugeRegion d N}
    {regionsSmall : CMP99SourceActiveRegionChain d M N OmegaSmall depth}
    {regionsLarge : CMP99SourceActiveRegionChain d M N OmegaLarge depth}
    (H : CMP99SourceNestedRegionChains d M regionsSmall regionsLarge)
    (hd : 2 ≤ d) (hM : 2 ≤ M) (rho : SUNAdjointModel Nc)
    (spacing epsilon : ℝ) (background : GaugeConfig d N (SUN Nc))
    (chain : CMP99SourceUbarRadiusChain d M Nc depth epsilon)
    (fineSmall : ∀ e : ConcreteEdge d N,
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon) :
    ‖H.terminalRestriction hd hM rho spacing epsilon background chain
      fineSmall‖ ≤ 1 := by
  letI : NeZero N := regionsSmall.neZero
  exact (Classical.choose_spec
    (H.exists_terminalRestriction_intertwining hd hM rho spacing epsilon
      background chain fineSmall)).2.2

/-- Terminal restriction for the canonical iterated lifts of two nested
source regions. -/
noncomputable def cmp99SourceIteratedLiftTerminalRestriction
    [NeZero N] {OmegaSmall OmegaLarge : ActiveGaugeRegion d N}
    (hsub : OmegaSmall.sites ⊆ OmegaLarge.sites)
    (hd : 2 ≤ d) (hM : 2 ≤ M) (rho : SUNAdjointModel Nc)
    (depth : ℕ) (spacing epsilon : ℝ)
    (background : GaugeConfig d
      (cmp99RegionalLatticeSize M N depth) (SUN Nc))
    (chain : CMP99SourceUbarRadiusChain d M Nc depth epsilon)
    (fineSmall : ∀ e : ConcreteEdge d
      (cmp99RegionalLatticeSize M N depth),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon) :
    let regionsSmall := cmp99SourceIteratedLiftActiveRegionChain
      (M := M) OmegaSmall depth
    let regionsLarge := cmp99SourceIteratedLiftActiveRegionChain
      (M := M) OmegaLarge depth
    let Tsmall := regionsSmall.weightedQprimeTower hd hM rho spacing epsilon
      background chain fineSmall
    let Tlarge := regionsLarge.weightedQprimeTower hd hM rho spacing epsilon
      background chain fineSmall
    Tlarge.TerminalSpace.carrier →L[ℝ] Tsmall.TerminalSpace.carrier :=
  (cmp99SourceIteratedLift_nestedRegionChains (M := M) hsub depth)
    |>.terminalRestriction hd hM rho spacing epsilon background chain fineSmall

/-- The canonical terminal restriction between iterated source lifts is a
counting-Hilbert contraction. -/
theorem norm_cmp99SourceIteratedLiftTerminalRestriction_le_one
    [NeZero N] {OmegaSmall OmegaLarge : ActiveGaugeRegion d N}
    (hsub : OmegaSmall.sites ⊆ OmegaLarge.sites)
    (hd : 2 ≤ d) (hM : 2 ≤ M) (rho : SUNAdjointModel Nc)
    (depth : ℕ) (spacing epsilon : ℝ)
    (background : GaugeConfig d
      (cmp99RegionalLatticeSize M N depth) (SUN Nc))
    (chain : CMP99SourceUbarRadiusChain d M Nc depth epsilon)
    (fineSmall : ∀ e : ConcreteEdge d
      (cmp99RegionalLatticeSize M N depth),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon) :
    ‖cmp99SourceIteratedLiftTerminalRestriction hsub hd hM rho depth spacing
      epsilon background chain fineSmall‖ ≤ 1 := by
  exact (cmp99SourceIteratedLift_nestedRegionChains (M := M) hsub depth)
    |>.norm_terminalRestriction_le_one hd hM rho spacing epsilon background
      chain fineSmall

/-- Exact `Q'` transition for canonical iterated source lifts. -/
theorem cmp99SourceIteratedLift_Qprime_transition
    [NeZero N] {OmegaSmall OmegaLarge : ActiveGaugeRegion d N}
    (hsub : OmegaSmall.sites ⊆ OmegaLarge.sites)
    (hd : 2 ≤ d) (hM : 2 ≤ M) (rho : SUNAdjointModel Nc)
    (depth : ℕ) (spacing epsilon : ℝ)
    (background : GaugeConfig d
      (cmp99RegionalLatticeSize M N depth) (SUN Nc))
    (chain : CMP99SourceUbarRadiusChain d M Nc depth epsilon)
    (fineSmall : ∀ e : ConcreteEdge d
      (cmp99RegionalLatticeSize M N depth),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon) :
    let regionsSmall := cmp99SourceIteratedLiftActiveRegionChain
      (M := M) OmegaSmall depth
    let regionsLarge := cmp99SourceIteratedLiftActiveRegionChain
      (M := M) OmegaLarge depth
    let Tsmall := regionsSmall.weightedQprimeTower hd hM rho spacing epsilon
      background chain fineSmall
    let Tlarge := regionsLarge.weightedQprimeTower hd hM rho spacing epsilon
      background chain fineSmall
    let Rfine := cmp99NestedActiveRegionRestriction
      (g := SUNLieCoord Nc)
      (cmp99IteratedLiftActiveRegion (M := M) OmegaSmall depth)
      (cmp99IteratedLiftActiveRegion (M := M) OmegaLarge depth)
    Tsmall.Qprime.comp Rfine =
      (cmp99SourceIteratedLiftTerminalRestriction hsub hd hM rho depth spacing
        epsilon background chain fineSmall).comp Tlarge.Qprime := by
  exact (cmp99SourceIteratedLift_nestedRegionChains (M := M) hsub depth)
    |>.Qprime_comp_restriction hd hM rho spacing epsilon background chain
      fineSmall

/-- Exact weighted-adjoint transition for canonical iterated source lifts. -/
theorem cmp99SourceIteratedLift_weightedAdjoint_transition
    [NeZero N] {OmegaSmall OmegaLarge : ActiveGaugeRegion d N}
    (hsub : OmegaSmall.sites ⊆ OmegaLarge.sites)
    (hd : 2 ≤ d) (hM : 2 ≤ M) (rho : SUNAdjointModel Nc)
    (depth : ℕ) (spacing epsilon : ℝ)
    (background : GaugeConfig d
      (cmp99RegionalLatticeSize M N depth) (SUN Nc))
    (chain : CMP99SourceUbarRadiusChain d M Nc depth epsilon)
    (fineSmall : ∀ e : ConcreteEdge d
      (cmp99RegionalLatticeSize M N depth),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon) :
    let regionsSmall := cmp99SourceIteratedLiftActiveRegionChain
      (M := M) OmegaSmall depth
    let regionsLarge := cmp99SourceIteratedLiftActiveRegionChain
      (M := M) OmegaLarge depth
    let Tsmall := regionsSmall.weightedQprimeTower hd hM rho spacing epsilon
      background chain fineSmall
    let Tlarge := regionsLarge.weightedQprimeTower hd hM rho spacing epsilon
      background chain fineSmall
    let Rfine := cmp99NestedActiveRegionRestriction
      (g := SUNLieCoord Nc)
      (cmp99IteratedLiftActiveRegion (M := M) OmegaSmall depth)
      (cmp99IteratedLiftActiveRegion (M := M) OmegaLarge depth)
    Rfine.comp Tlarge.weightedAdjoint = Tsmall.weightedAdjoint.comp
      (cmp99SourceIteratedLiftTerminalRestriction hsub hd hM rho depth spacing
        epsilon background chain fineSmall) := by
  exact (cmp99SourceIteratedLift_nestedRegionChains (M := M) hsub depth)
    |>.restriction_comp_weightedAdjoint hd hM rho spacing epsilon background
      chain fineSmall

universe v

namespace CMP99SourceDependentOmegaGeometry

variable {Q j : ℕ} [NeZero Q]
variable {cell : FinBox 4 Q}
variable {ScaleSite : Fin (j + 2) → Type v}
variable [∀ r, DecidableEq (ScaleSite r)]
variable {Scaled : CMP99SourceScaledStratification
  (FinBox 4 (2 * Q)) (j + 2) ScaleSite}
variable {dist : FinBox 4 (2 * Q) → FinBox 4 (2 * Q) → ℕ}
variable {gap : Fin (j + 1) → ℕ}

/-- Terminal restriction produced by the literal consecutive generated
`Omega` towers. -/
noncomputable def generatedTerminalRestriction
    (D : CMP99SourceDependentOmegaGeometry
      (FinBox 4 (2 * Q)) j ScaleSite Scaled
      (cmp99SourceTildePiLargeBlocks cell 3)
      (cmp99SourceTildePiLargeBlocks cell 4) dist gap)
    (hpi5 : D.fineRegion (cmp99OmegaZeroIndex j) ⊆
      cmp99SourceTildePiLargeBlocks cell 5)
    (r : Fin (j + 1)) (hM : 2 ≤ M) (depth : ℕ)
    (spacing epsilon : ℝ)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 M Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon) :
    let regionsSmall := cmp99SourceIteratedLiftActiveRegionChain (M := M)
      (D.operatorCoarseRegion hpi5 (cmp99OmegaTransitionNextIndex r))
      (depth + 1)
    let regionsLarge := cmp99SourceIteratedLiftActiveRegionChain (M := M)
      (D.operatorCoarseRegion hpi5 (cmp99OmegaTransitionIndex r))
      (depth + 1)
    let Tsmall := regionsSmall.weightedQprimeTower (by norm_num) hM
      (matrixSUNAdjointModel Nc) spacing epsilon background
      budget.toRadiusChain fineSmall
    let Tlarge := regionsLarge.weightedQprimeTower (by norm_num) hM
      (matrixSUNAdjointModel Nc) spacing epsilon background
      budget.toRadiusChain fineSmall
    Tlarge.TerminalSpace.carrier →L[ℝ] Tsmall.TerminalSpace.carrier := by
  have hsub :
      (D.operatorCoarseRegion hpi5
          (cmp99OmegaTransitionNextIndex r)).sites ⊆
        (D.operatorCoarseRegion hpi5
          (cmp99OmegaTransitionIndex r)).sites := by
    change D.fineRegion (cmp99OmegaTransitionNextIndex r) ⊆
      D.fineRegion (cmp99OmegaTransitionIndex r)
    exact D.fineRegion_subset_of_le (by
      change r.val ≤ r.val + 1
      omega)
  exact cmp99SourceIteratedLiftTerminalRestriction hsub (by norm_num) hM
    (matrixSUNAdjointModel Nc) (depth + 1) spacing epsilon background
    budget.toRadiusChain fineSmall

/-- The complete generated terminal restriction is contractive uniformly in
the number of generated scales and in the ambient volume. -/
theorem norm_generatedTerminalRestriction_le_one
    (D : CMP99SourceDependentOmegaGeometry
      (FinBox 4 (2 * Q)) j ScaleSite Scaled
      (cmp99SourceTildePiLargeBlocks cell 3)
      (cmp99SourceTildePiLargeBlocks cell 4) dist gap)
    (hpi5 : D.fineRegion (cmp99OmegaZeroIndex j) ⊆
      cmp99SourceTildePiLargeBlocks cell 5)
    (r : Fin (j + 1)) (hM : 2 ≤ M) (depth : ℕ)
    (spacing epsilon : ℝ)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 M Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon) :
    ‖D.generatedTerminalRestriction hpi5 r hM depth spacing epsilon
      background budget fineSmall‖ ≤ 1 := by
  have hsub :
      (D.operatorCoarseRegion hpi5
          (cmp99OmegaTransitionNextIndex r)).sites ⊆
        (D.operatorCoarseRegion hpi5
          (cmp99OmegaTransitionIndex r)).sites := by
    change D.fineRegion (cmp99OmegaTransitionNextIndex r) ⊆
      D.fineRegion (cmp99OmegaTransitionIndex r)
    exact D.fineRegion_subset_of_le (by
      change r.val ≤ r.val + 1
      omega)
  simpa [generatedTerminalRestriction] using
    (norm_cmp99SourceIteratedLiftTerminalRestriction_le_one hsub
      (show 2 ≤ 4 by norm_num) hM (matrixSUNAdjointModel Nc) (depth + 1)
      spacing epsilon background budget.toRadiusChain fineSmall)

set_option maxHeartbeats 1000000 in
/-- Exact generated `Q'` transition on consecutive physical domains. -/
theorem generatedQprime_transition
    (D : CMP99SourceDependentOmegaGeometry
      (FinBox 4 (2 * Q)) j ScaleSite Scaled
      (cmp99SourceTildePiLargeBlocks cell 3)
      (cmp99SourceTildePiLargeBlocks cell 4) dist gap)
    (hpi5 : D.fineRegion (cmp99OmegaZeroIndex j) ⊆
      cmp99SourceTildePiLargeBlocks cell 5)
    (r : Fin (j + 1)) (hM : 2 ≤ M) (depth : ℕ)
    (spacing epsilon : ℝ)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 M Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon) :
    let regionsSmall := cmp99SourceIteratedLiftActiveRegionChain (M := M)
      (D.operatorCoarseRegion hpi5 (cmp99OmegaTransitionNextIndex r))
      (depth + 1)
    let regionsLarge := cmp99SourceIteratedLiftActiveRegionChain (M := M)
      (D.operatorCoarseRegion hpi5 (cmp99OmegaTransitionIndex r))
      (depth + 1)
    let Tsmall := regionsSmall.weightedQprimeTower (by norm_num) hM
      (matrixSUNAdjointModel Nc) spacing epsilon background
      budget.toRadiusChain fineSmall
    let Tlarge := regionsLarge.weightedQprimeTower (by norm_num) hM
      (matrixSUNAdjointModel Nc) spacing epsilon background
      budget.toRadiusChain fineSmall
    Tsmall.Qprime.comp
        (D.generatedTransitionRestriction (M := M) (Nc := Nc) hpi5 r
          (depth + 1)) =
      (D.generatedTerminalRestriction hpi5 r hM depth spacing epsilon
        background budget fineSmall).comp Tlarge.Qprime := by
  have hsub :
      (D.operatorCoarseRegion hpi5
          (cmp99OmegaTransitionNextIndex r)).sites ⊆
        (D.operatorCoarseRegion hpi5
          (cmp99OmegaTransitionIndex r)).sites := by
    change D.fineRegion (cmp99OmegaTransitionNextIndex r) ⊆
      D.fineRegion (cmp99OmegaTransitionIndex r)
    exact D.fineRegion_subset_of_le (by
      change r.val ≤ r.val + 1
      omega)
  simpa [generatedTransitionRestriction, cmp99NestedActiveRegionRestriction,
    operatorRegion, generatedTerminalRestriction] using
    (cmp99SourceIteratedLift_Qprime_transition hsub (by norm_num) hM
      (matrixSUNAdjointModel Nc) (depth + 1) spacing epsilon background
      budget.toRadiusChain fineSmall)

set_option maxHeartbeats 1000000 in
/-- Exact generated weighted-adjoint transition on consecutive physical
domains. -/
theorem generatedWeightedAdjoint_transition
    (D : CMP99SourceDependentOmegaGeometry
      (FinBox 4 (2 * Q)) j ScaleSite Scaled
      (cmp99SourceTildePiLargeBlocks cell 3)
      (cmp99SourceTildePiLargeBlocks cell 4) dist gap)
    (hpi5 : D.fineRegion (cmp99OmegaZeroIndex j) ⊆
      cmp99SourceTildePiLargeBlocks cell 5)
    (r : Fin (j + 1)) (hM : 2 ≤ M) (depth : ℕ)
    (spacing epsilon : ℝ)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 M Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon) :
    let regionsSmall := cmp99SourceIteratedLiftActiveRegionChain (M := M)
      (D.operatorCoarseRegion hpi5 (cmp99OmegaTransitionNextIndex r))
      (depth + 1)
    let regionsLarge := cmp99SourceIteratedLiftActiveRegionChain (M := M)
      (D.operatorCoarseRegion hpi5 (cmp99OmegaTransitionIndex r))
      (depth + 1)
    let Tsmall := regionsSmall.weightedQprimeTower (by norm_num) hM
      (matrixSUNAdjointModel Nc) spacing epsilon background
      budget.toRadiusChain fineSmall
    let Tlarge := regionsLarge.weightedQprimeTower (by norm_num) hM
      (matrixSUNAdjointModel Nc) spacing epsilon background
      budget.toRadiusChain fineSmall
    (D.generatedTransitionRestriction (M := M) (Nc := Nc) hpi5 r
        (depth + 1)).comp Tlarge.weightedAdjoint =
      Tsmall.weightedAdjoint.comp
        (D.generatedTerminalRestriction hpi5 r hM depth spacing epsilon
          background budget fineSmall) := by
  have hsub :
      (D.operatorCoarseRegion hpi5
          (cmp99OmegaTransitionNextIndex r)).sites ⊆
        (D.operatorCoarseRegion hpi5
          (cmp99OmegaTransitionIndex r)).sites := by
    change D.fineRegion (cmp99OmegaTransitionNextIndex r) ⊆
      D.fineRegion (cmp99OmegaTransitionIndex r)
    exact D.fineRegion_subset_of_le (by
      change r.val ≤ r.val + 1
      omega)
  simpa [generatedTransitionRestriction, cmp99NestedActiveRegionRestriction,
    operatorRegion, generatedTerminalRestriction] using
    (cmp99SourceIteratedLift_weightedAdjoint_transition hsub (by norm_num) hM
      (matrixSUNAdjointModel Nc) (depth + 1) spacing epsilon background
      budget.toRadiusChain fineSmall)

end CMP99SourceDependentOmegaGeometry

end

end YangMills.RG
