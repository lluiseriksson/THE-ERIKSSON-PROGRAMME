/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceGeneratedRegionTransition

/-!
# Exact regional transition of the generated CMP99 mass

The generated precision contains the counting-Hilbert mass `Q'^* Q'`.
This file first proves the exact restriction identities for one physical
regional average on arbitrary nested complete-block regions.  These lemmas
are independent of a fixed `Omega` sequence and therefore apply at every
level of the generated source tower.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator RealInnerProductSpace

noncomputable section

/-- Restriction between arbitrary active regions on one ambient lattice. -/
noncomputable def cmp99NestedActiveRegionRestriction
    {d N : ℕ} {g : Type*} [NeZero N]
    [NormedAddCommGroup g] [InnerProductSpace ℝ g]
    [FiniteDimensional ℝ g]
    (OmegaSmall OmegaLarge : ActiveGaugeRegion d N) :
    ActiveGaugeZeroCochain OmegaLarge g →L[ℝ]
      ActiveGaugeZeroCochain OmegaSmall g :=
  (restrictZeroCLM OmegaSmall).comp (extendZeroZeroCLM OmegaLarge)

/-- A transported block average commutes exactly with restriction between
arbitrary nested complete-block regions. -/
theorem cmp99SourceTransportedBlockAverage_nested_transition
    {d M N : ℕ} {g : Type*} [NeZero M] [NeZero N]
    [NormedAddCommGroup g] [InnerProductSpace ℝ g]
    [FiniteDimensional ℝ g]
    (OmegaSmall OmegaLarge : ActiveGaugeRegion d (M * N))
    (hsub : OmegaSmall.sites ⊆ OmegaLarge.sites)
    (transport : FinBox d N → FinBox d (M * N) → (g ≃ₗᵢ[ℝ] g)) :
    (cmp99SourceTransportedBlockAverageCLM OmegaSmall transport).comp
        (cmp99NestedActiveRegionRestriction OmegaSmall OmegaLarge) =
      (cmp99NestedActiveRegionRestriction
        (cmp99ActiveCoarseRegion (M := M) (N' := N) OmegaSmall)
        (cmp99ActiveCoarseRegion (M := M) (N' := N) OmegaLarge)).comp
        (cmp99SourceTransportedBlockAverageCLM OmegaLarge transport) := by
  apply ContinuousLinearMap.ext
  intro phi
  ext y
  have hySmall : blockOf M N y.1 ⊆ OmegaSmall.sites :=
    (mem_cmp99ActiveCoarseRegion_sites_iff OmegaSmall y.1).mp y.2
  have hyLarge : blockOf M N y.1 ⊆ OmegaLarge.sites := fun x hx =>
    hsub (hySmall hx)
  have hyLargeMem : y.1 ∈
      (cmp99ActiveCoarseRegion (M := M) (N' := N) OmegaLarge).sites :=
    (mem_cmp99ActiveCoarseRegion_sites_iff OmegaLarge y.1).mpr hyLarge
  let yLarge : ActiveGaugeRegion.Site
      (cmp99ActiveCoarseRegion (M := M) (N' := N) OmegaLarge) :=
    ⟨y.1, hyLargeMem⟩
  have hcoarse :
      cmp99NestedActiveRegionRestriction
          (cmp99ActiveCoarseRegion (M := M) (N' := N) OmegaSmall)
          (cmp99ActiveCoarseRegion (M := M) (N' := N) OmegaLarge)
          (cmp99SourceTransportedBlockAverageCLM OmegaLarge transport phi) y =
        cmp99SourceTransportedBlockAverageCLM OmegaLarge transport phi yLarge := by
    change (if h : y.1 ∈
        (cmp99ActiveCoarseRegion (M := M) (N' := N) OmegaLarge).sites then
          cmp99SourceTransportedBlockAverageCLM OmegaLarge transport phi
            ⟨y.1, h⟩ else 0) = _
    rw [dif_pos hyLargeMem]
  simp only [ContinuousLinearMap.comp_apply]
  rw [hcoarse]
  simp only [cmp99SourceTransportedBlockAverageCLM,
    cmp99TransportedBlockAverageCLM_apply]
  apply congrArg (fun z : g => cmp99SourceBlockAverageWeight M d • z)
  apply Finset.sum_congr rfl
  intro x _hx
  apply congrArg (transport y.1 x.1)
  have hxSmall : x.1 ∈ OmegaSmall.sites := hySmall x.2
  have hxLarge : x.1 ∈ OmegaLarge.sites := hsub hxSmall
  change (if h : x.1 ∈ OmegaLarge.sites then phi ⟨x.1, h⟩ else 0) =
    phi (cmp99ActiveFineSiteOfBlock OmegaLarge yLarge x)
  rw [dif_pos hxLarge]
  rfl

/-- The counting-Hilbert adjoints of the same arbitrary nested averages
commute with fine and coarse restriction. -/
theorem cmp99SourceTransportedBlockAverage_adjoint_nested_transition
    {d M N : ℕ} {g : Type*} [NeZero M] [NeZero N]
    [NormedAddCommGroup g] [InnerProductSpace ℝ g]
    [FiniteDimensional ℝ g]
    (OmegaSmall OmegaLarge : ActiveGaugeRegion d (M * N))
    (hSmall : OmegaSmall.BlockSaturated)
    (hLarge : OmegaLarge.BlockSaturated)
    (hsub : OmegaSmall.sites ⊆ OmegaLarge.sites)
    (transport : FinBox d N → FinBox d (M * N) → (g ≃ₗᵢ[ℝ] g)) :
    (cmp99NestedActiveRegionRestriction OmegaSmall OmegaLarge).comp
        (cmp99SourceTransportedBlockAverageCLM OmegaLarge transport).adjoint =
      (cmp99SourceTransportedBlockAverageCLM OmegaSmall transport).adjoint.comp
        (cmp99NestedActiveRegionRestriction
          (cmp99ActiveCoarseRegion (M := M) (N' := N) OmegaSmall)
          (cmp99ActiveCoarseRegion (M := M) (N' := N) OmegaLarge)) := by
  rw [cmp99SourceTransportedBlockAverageCLM,
    cmp99SourceTransportedBlockAverageCLM,
    ← cmp99TransportedBlockSynthesisCLM_eq_adjoint OmegaLarge hLarge
      (cmp99SourceBlockAverageWeight M d) transport,
    ← cmp99TransportedBlockSynthesisCLM_eq_adjoint OmegaSmall hSmall
      (cmp99SourceBlockAverageWeight M d) transport]
  apply ContinuousLinearMap.ext
  intro eta
  ext x
  have hxSmall : x.1 ∈ OmegaSmall.sites := x.2
  have hxLarge : x.1 ∈ OmegaLarge.sites := hsub hxSmall
  have hySmall : blockSite M N x.1 ∈
      (cmp99ActiveCoarseRegion (M := M) (N' := N) OmegaSmall).sites :=
    (mem_cmp99ActiveCoarseRegion_sites_iff OmegaSmall _).mpr
      (hSmall x.1 hxSmall)
  have hyLarge : blockSite M N x.1 ∈
      (cmp99ActiveCoarseRegion (M := M) (N' := N) OmegaLarge).sites :=
    (mem_cmp99ActiveCoarseRegion_sites_iff OmegaLarge _).mpr
      (hLarge x.1 hxLarge)
  let xLarge : ActiveGaugeRegion.Site OmegaLarge := ⟨x.1, hxLarge⟩
  let ySmall : ActiveGaugeRegion.Site
      (cmp99ActiveCoarseRegion (M := M) (N' := N) OmegaSmall) :=
    ⟨blockSite M N x.1, hySmall⟩
  let yLarge : ActiveGaugeRegion.Site
      (cmp99ActiveCoarseRegion (M := M) (N' := N) OmegaLarge) :=
    ⟨blockSite M N x.1, hyLarge⟩
  have hfine :
      cmp99NestedActiveRegionRestriction OmegaSmall OmegaLarge
          (cmp99TransportedBlockSynthesisCLM OmegaLarge hLarge
            (cmp99SourceBlockAverageWeight M d) transport eta) x =
        cmp99TransportedBlockSynthesisCLM OmegaLarge hLarge
          (cmp99SourceBlockAverageWeight M d) transport eta xLarge := by
    change (if h : x.1 ∈ OmegaLarge.sites then
        cmp99TransportedBlockSynthesisCLM OmegaLarge hLarge
          (cmp99SourceBlockAverageWeight M d) transport eta ⟨x.1, h⟩
      else 0) = _
    rw [dif_pos hxLarge]
  have hcoarse :
      cmp99NestedActiveRegionRestriction
          (cmp99ActiveCoarseRegion (M := M) (N' := N) OmegaSmall)
          (cmp99ActiveCoarseRegion (M := M) (N' := N) OmegaLarge)
          eta ySmall = eta yLarge := by
    change (if h : blockSite M N x.1 ∈
        (cmp99ActiveCoarseRegion (M := M) (N' := N) OmegaLarge).sites then
          eta ⟨blockSite M N x.1, h⟩ else 0) = _
    rw [dif_pos hyLarge]
  simp only [ContinuousLinearMap.comp_apply]
  rw [hfine, cmp99TransportedBlockSynthesisCLM_apply,
    cmp99TransportedBlockSynthesisCLM_apply]
  change cmp99SourceBlockAverageWeight M d •
      (transport (blockSite M N xLarge.1) xLarge.1).symm (eta yLarge) =
    cmp99SourceBlockAverageWeight M d •
      (transport (blockSite M N x.1) x.1).symm
        (cmp99NestedActiveRegionRestriction
          (cmp99ActiveCoarseRegion (M := M) (N' := N) OmegaSmall)
          (cmp99ActiveCoarseRegion (M := M) (N' := N) OmegaLarge) eta ySmall)
  rw [hcoarse]

/-- Consequently the complete one-step counting-Hilbert mass commutes with
restriction on arbitrary nested source regions. -/
theorem cmp99SourceTransportedBlockMass_nested_transition
    {d M N : ℕ} {g : Type*} [NeZero M] [NeZero N]
    [NormedAddCommGroup g] [InnerProductSpace ℝ g]
    [FiniteDimensional ℝ g]
    (OmegaSmall OmegaLarge : ActiveGaugeRegion d (M * N))
    (hSmall : OmegaSmall.BlockSaturated)
    (hLarge : OmegaLarge.BlockSaturated)
    (hsub : OmegaSmall.sites ⊆ OmegaLarge.sites)
    (transport : FinBox d N → FinBox d (M * N) → (g ≃ₗᵢ[ℝ] g)) :
    (cmp99NestedActiveRegionRestriction OmegaSmall OmegaLarge).comp
        ((cmp99SourceTransportedBlockAverageCLM OmegaLarge transport).adjoint.comp
          (cmp99SourceTransportedBlockAverageCLM OmegaLarge transport)) =
      ((cmp99SourceTransportedBlockAverageCLM OmegaSmall transport).adjoint.comp
        (cmp99SourceTransportedBlockAverageCLM OmegaSmall transport)).comp
          (cmp99NestedActiveRegionRestriction OmegaSmall OmegaLarge) := by
  let Qlarge := cmp99SourceTransportedBlockAverageCLM OmegaLarge transport
  let Qsmall := cmp99SourceTransportedBlockAverageCLM OmegaSmall transport
  let Rfine := cmp99NestedActiveRegionRestriction (g := g)
    OmegaSmall OmegaLarge
  let Rcoarse := cmp99NestedActiveRegionRestriction (g := g)
    (cmp99ActiveCoarseRegion (M := M) (N' := N) OmegaSmall)
    (cmp99ActiveCoarseRegion (M := M) (N' := N) OmegaLarge)
  have hQ : Qsmall.comp Rfine = Rcoarse.comp Qlarge :=
    cmp99SourceTransportedBlockAverage_nested_transition
      OmegaSmall OmegaLarge hsub transport
  have hQstar : Rfine.comp Qlarge.adjoint =
      Qsmall.adjoint.comp Rcoarse :=
    cmp99SourceTransportedBlockAverage_adjoint_nested_transition
      OmegaSmall OmegaLarge hSmall hLarge hsub transport
  change Rfine.comp (Qlarge.adjoint.comp Qlarge) =
    (Qsmall.adjoint.comp Qsmall).comp Rfine
  calc
    Rfine.comp (Qlarge.adjoint.comp Qlarge) =
        (Rfine.comp Qlarge.adjoint).comp Qlarge := by
      rw [ContinuousLinearMap.comp_assoc]
    _ = (Qsmall.adjoint.comp Rcoarse).comp Qlarge := by rw [hQstar]
    _ = Qsmall.adjoint.comp (Rcoarse.comp Qlarge) := by
      rw [ContinuousLinearMap.comp_assoc]
    _ = Qsmall.adjoint.comp (Qsmall.comp Rfine) := by rw [hQ]
    _ = (Qsmall.adjoint.comp Qsmall).comp Rfine := by
      rw [ContinuousLinearMap.comp_assoc]

/-- The counting-Hilbert mass of a regional tower step factors through the
tail mass and the literal head average. -/
theorem CMP99SourceWeightedRegionalTower.countingMass_step
    {d M N : ℕ} {g : Type} [NeZero M] [NeZero N]
    [NormedAddCommGroup g] [InnerProductSpace ℝ g]
    [FiniteDimensional ℝ g]
    (Omega : ActiveGaugeRegion d (M * N))
    (hOmega : Omega.BlockSaturated) (spacing : ℝ)
    (transport : FinBox d N → FinBox d (M * N) → (g ≃ₗᵢ[ℝ] g))
    (tail : CMP99SourceWeightedRegionalTower (g := g)
      (cmp99ActiveCoarseRegion (M := M) (N' := N) Omega)
      ((M : ℝ) * spacing)) :
    let Qhead := cmp99SourceTransportedBlockAverageCLM Omega transport
    let T := CMP99SourceWeightedRegionalTower.step
      Omega hOmega spacing transport tail
    T.Qprime.adjoint.comp T.Qprime =
      Qhead.adjoint.comp
        ((tail.Qprime.adjoint.comp tail.Qprime).comp Qhead) := by
  dsimp only
  rw [CMP99SourceWeightedRegionalTower.Qprime_step]
  let Qhead := cmp99SourceTransportedBlockAverageCLM Omega transport
  have hadj : (tail.Qprime.comp Qhead).adjoint =
      Qhead.adjoint.comp tail.Qprime.adjoint :=
    ContinuousLinearMap.adjoint_comp tail.Qprime Qhead
  calc
    (tail.Qprime.comp Qhead).adjoint.comp (tail.Qprime.comp Qhead) =
        (Qhead.adjoint.comp tail.Qprime.adjoint).comp
          (tail.Qprime.comp Qhead) :=
      congrArg (fun A => A.comp (tail.Qprime.comp Qhead)) hadj
    _ = Qhead.adjoint.comp
        ((tail.Qprime.adjoint.comp tail.Qprime).comp Qhead) := by
      simp only [ContinuousLinearMap.comp_assoc]

/-- Algebraic induction step: intertwining the head average and the tail
mass intertwines the complete composed mass. -/
theorem cmp99NestedComposedMass_transition
    {Elarge Esmall Flarge Fsmall : Type*}
    [NormedAddCommGroup Elarge] [InnerProductSpace ℝ Elarge]
    [CompleteSpace Elarge]
    [NormedAddCommGroup Esmall] [InnerProductSpace ℝ Esmall]
    [CompleteSpace Esmall]
    [NormedAddCommGroup Flarge] [InnerProductSpace ℝ Flarge]
    [CompleteSpace Flarge]
    [NormedAddCommGroup Fsmall] [InnerProductSpace ℝ Fsmall]
    [CompleteSpace Fsmall]
    (Qlarge : Elarge →L[ℝ] Flarge) (Qsmall : Esmall →L[ℝ] Fsmall)
    (Mlarge : Flarge →L[ℝ] Flarge) (Msmall : Fsmall →L[ℝ] Fsmall)
    (Rfine : Elarge →L[ℝ] Esmall) (Rcoarse : Flarge →L[ℝ] Fsmall)
    (hQ : Qsmall.comp Rfine = Rcoarse.comp Qlarge)
    (hQstar : Rfine.comp Qlarge.adjoint = Qsmall.adjoint.comp Rcoarse)
    (hM : Rcoarse.comp Mlarge = Msmall.comp Rcoarse) :
    Rfine.comp (Qlarge.adjoint.comp (Mlarge.comp Qlarge)) =
      (Qsmall.adjoint.comp (Msmall.comp Qsmall)).comp Rfine := by
  calc
    Rfine.comp (Qlarge.adjoint.comp (Mlarge.comp Qlarge)) =
        (Rfine.comp Qlarge.adjoint).comp (Mlarge.comp Qlarge) := by
      rw [ContinuousLinearMap.comp_assoc]
    _ = (Qsmall.adjoint.comp Rcoarse).comp (Mlarge.comp Qlarge) := by
      rw [hQstar]
    _ = Qsmall.adjoint.comp ((Rcoarse.comp Mlarge).comp Qlarge) := by
      simp only [ContinuousLinearMap.comp_assoc]
    _ = Qsmall.adjoint.comp ((Msmall.comp Rcoarse).comp Qlarge) := by
      rw [hM]
    _ = Qsmall.adjoint.comp (Msmall.comp (Rcoarse.comp Qlarge)) := by
      simp only [ContinuousLinearMap.comp_assoc]
    _ = Qsmall.adjoint.comp (Msmall.comp (Qsmall.comp Rfine)) := by
      rw [hQ]
    _ = (Qsmall.adjoint.comp (Msmall.comp Qsmall)).comp Rfine := by
      simp only [ContinuousLinearMap.comp_assoc]

variable {d M N Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero Nc]

/-- Recursive counting-Hilbert mass generated by one typed physical source
region chain.  This definition exposes the exact induction structure hidden
inside `Q'^* Q'`. -/
noncomputable def CMP99SourceActiveRegionChain.generatedCountingMass
    {N depth : ℕ} {Omega : ActiveGaugeRegion d N}
    (regions : CMP99SourceActiveRegionChain d M N Omega depth)
    (hd : 2 ≤ d) (hM : 2 ≤ M)
    (rho : SUNAdjointModel Nc) :
    letI : NeZero N := regions.neZero
    (spacing epsilon : ℝ) → (background : GaugeConfig d N (SUN Nc)) →
    (chain : CMP99SourceUbarRadiusChain d M Nc depth epsilon) →
    (fineSmall : ∀ e : ConcreteEdge d N,
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon) →
    ActiveGaugeZeroCochain Omega (SUNLieCoord Nc) →L[ℝ]
      ActiveGaugeZeroCochain Omega (SUNLieCoord Nc) := by
  letI : NeZero N := regions.neZero
  intro spacing epsilon background chain fineSmall
  induction regions generalizing spacing epsilon with
  | stop Omega =>
      exact ContinuousLinearMap.id ℝ _
  | @step N' depth _ Omega hOmega tail ih =>
      letI : NeZero (M * N') := inferInstance
      let Scale : CMP99SourceNormalizedRegionalScale Omega background :=
        CMP99SourceNormalizedRegionalScale.ofFineSmall hd hM Omega background
          hOmega epsilon chain.epsilon_nonneg chain.head_noWinding fineSmall
      have nextSmall : ∀ e : ConcreteEdge d N',
          ‖(Scale.toSourceScale.data.nextBackground e :
              Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤
            cmp99SourceUbarNextFineRadius d M epsilon := by
        intro e
        simpa [Scale, CMP99SourceNormalizedRegionalScale.ofFineSmall,
          CMP99SourceRegionalScale.ofFineSmall] using
          norm_cmp99SourceRegionalScaleDataOfFineSmall_nextBackground_sub_one_le
            hd hM Omega background (cmp99SourceBlockAverageWeight M d)
            epsilon chain.epsilon_nonneg chain.head_noWinding
            chain.head_logSmall fineSmall e
      let Qhead := cmp99SourceTransportedBlockAverageCLM Omega
        (cmp99SourceWeightedPhysicalTransport rho background)
      exact Qhead.adjoint.comp
        ((ih ((M : ℝ) * spacing)
          (cmp99SourceUbarNextFineRadius d M epsilon)
          Scale.toSourceScale.data.nextBackground chain.tail nextSmall).comp
            Qhead)

/-- The recursive mass is exactly the counting-Hilbert mass of the literal
generated `Q'_j`; it is not a replacement operator. -/
theorem CMP99SourceActiveRegionChain.generatedCountingMass_eq_QprimeMass
    {depth : ℕ} {Omega : ActiveGaugeRegion d N}
    (regions : CMP99SourceActiveRegionChain d M N Omega depth)
    (hd : 2 ≤ d) (hM : 2 ≤ M) (rho : SUNAdjointModel Nc) :
    letI : NeZero N := regions.neZero
    ∀ (spacing epsilon : ℝ) (background : GaugeConfig d N (SUN Nc))
      (chain : CMP99SourceUbarRadiusChain d M Nc depth epsilon)
      (fineSmall : ∀ e : ConcreteEdge d N,
        ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon),
      regions.generatedCountingMass hd hM rho spacing epsilon background
          chain fineSmall =
        let T := regions.weightedQprimeTower hd hM rho spacing epsilon
          background chain fineSmall
        T.Qprime.adjoint.comp T.Qprime := by
  letI : NeZero N := regions.neZero
  induction regions with
  | stop Omega =>
      intro spacing epsilon background chain fineSmall
      change ContinuousLinearMap.id ℝ _ =
        (ContinuousLinearMap.id ℝ _).adjoint.comp
          (ContinuousLinearMap.id ℝ _)
      rw [ContinuousLinearMap.adjoint_id, ContinuousLinearMap.id_comp]
  | @step N' depth _ Omega hOmega tail ih =>
      intro spacing epsilon background chain fineSmall
      letI : NeZero (M * N') := inferInstance
      let Scale : CMP99SourceNormalizedRegionalScale Omega background :=
        CMP99SourceNormalizedRegionalScale.ofFineSmall hd hM Omega background
          hOmega epsilon chain.epsilon_nonneg chain.head_noWinding fineSmall
      have nextSmall : ∀ e : ConcreteEdge d N',
          ‖(Scale.toSourceScale.data.nextBackground e :
              Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤
            cmp99SourceUbarNextFineRadius d M epsilon := by
        intro e
        simpa [Scale, CMP99SourceNormalizedRegionalScale.ofFineSmall,
          CMP99SourceRegionalScale.ofFineSmall] using
          norm_cmp99SourceRegionalScaleDataOfFineSmall_nextBackground_sub_one_le
            hd hM Omega background (cmp99SourceBlockAverageWeight M d)
            epsilon chain.epsilon_nonneg chain.head_noWinding
            chain.head_logSmall fineSmall e
      let Qhead := cmp99SourceTransportedBlockAverageCLM Omega
        (cmp99SourceWeightedPhysicalTransport rho background)
      let tailTower := tail.weightedQprimeTower hd hM rho
        ((M : ℝ) * spacing) (cmp99SourceUbarNextFineRadius d M epsilon)
        Scale.toSourceScale.data.nextBackground chain.tail nextSmall
      change Qhead.adjoint.comp
          ((tail.generatedCountingMass hd hM rho ((M : ℝ) * spacing)
            (cmp99SourceUbarNextFineRadius d M epsilon)
            Scale.toSourceScale.data.nextBackground chain.tail nextSmall).comp
              Qhead) =
        (CMP99SourceWeightedRegionalTower.step Omega hOmega spacing
          (cmp99SourceWeightedPhysicalTransport rho background)
          tailTower).Qprime.adjoint.comp
          (CMP99SourceWeightedRegionalTower.step Omega hOmega spacing
            (cmp99SourceWeightedPhysicalTransport rho background)
            tailTower).Qprime
      rw [CMP99SourceWeightedRegionalTower.countingMass_step]
      rw [ih]

/-- Two typed regional chains are nested when their starting regions are
nested and their literal coarse tails are nested at every scale. -/
inductive CMP99SourceNestedRegionChains (d M : ℕ) [NeZero M] :
    {N depth : ℕ} →
    {OmegaSmall OmegaLarge : ActiveGaugeRegion d N} →
    CMP99SourceActiveRegionChain d M N OmegaSmall depth →
    CMP99SourceActiveRegionChain d M N OmegaLarge depth → Prop
  | stop {N : ℕ} [NeZero N]
      (OmegaSmall OmegaLarge : ActiveGaugeRegion d N)
      (hsub : OmegaSmall.sites ⊆ OmegaLarge.sites) :
      CMP99SourceNestedRegionChains d M
        (.stop OmegaSmall) (.stop OmegaLarge)
  | step {N depth : ℕ} [NeZero N]
      (OmegaSmall OmegaLarge : ActiveGaugeRegion d (M * N))
      (hSmall : OmegaSmall.BlockSaturated)
      (hLarge : OmegaLarge.BlockSaturated)
      (hsub : OmegaSmall.sites ⊆ OmegaLarge.sites)
      (tailSmall : CMP99SourceActiveRegionChain d M N
        (cmp99ActiveCoarseRegion (M := M) (N' := N) OmegaSmall) depth)
      (tailLarge : CMP99SourceActiveRegionChain d M N
        (cmp99ActiveCoarseRegion (M := M) (N' := N) OmegaLarge) depth)
      (tailNested : CMP99SourceNestedRegionChains d M tailSmall tailLarge) :
      CMP99SourceNestedRegionChains d M
        (.step OmegaSmall hSmall tailSmall) (.step OmegaLarge hLarge tailLarge)

omit [NeZero d] in
/-- Nestedness transports along equalities of the two indexed regions. -/
theorem CMP99SourceNestedRegionChains.cast_regions
    {N depth : ℕ} [NeZero N]
    {OmegaSmall OmegaLarge OmegaSmall' OmegaLarge' : ActiveGaugeRegion d N}
    {regionsSmall : CMP99SourceActiveRegionChain d M N OmegaSmall depth}
    {regionsLarge : CMP99SourceActiveRegionChain d M N OmegaLarge depth}
    (hSmall : OmegaSmall = OmegaSmall') (hLarge : OmegaLarge = OmegaLarge')
    (H : CMP99SourceNestedRegionChains d M regionsSmall regionsLarge) :
    CMP99SourceNestedRegionChains d M
      (hSmall ▸ regionsSmall) (hLarge ▸ regionsLarge) := by
  subst OmegaSmall'
  subst OmegaLarge'
  exact H

omit [NeZero d] in
/-- Canonical iterated lifts of nested source regions form nested typed
chains at every depth. -/
theorem cmp99SourceIteratedLift_nestedRegionChains
    [NeZero N] {OmegaSmall OmegaLarge : ActiveGaugeRegion d N}
    (hsub : OmegaSmall.sites ⊆ OmegaLarge.sites) :
    ∀ depth : ℕ,
      CMP99SourceNestedRegionChains d M
        (cmp99SourceIteratedLiftActiveRegionChain (M := M) OmegaSmall depth)
        (cmp99SourceIteratedLiftActiveRegionChain (M := M) OmegaLarge depth) := by
  intro depth
  induction depth with
  | zero => exact .stop OmegaSmall OmegaLarge hsub
  | succ depth ih =>
      let fineSmall :=
        cmp99IteratedLiftActiveRegion (M := M) OmegaSmall (depth + 1)
      let fineLarge :=
        cmp99IteratedLiftActiveRegion (M := M) OmegaLarge (depth + 1)
      have hSmall : fineSmall.BlockSaturated :=
        cmp99IteratedLiftActiveRegion_blockSaturated OmegaSmall depth
      have hLarge : fineLarge.BlockSaturated :=
        cmp99IteratedLiftActiveRegion_blockSaturated OmegaLarge depth
      have hFine : fineSmall.sites ⊆ fineLarge.sites :=
        cmp99IteratedLiftActiveRegion_sites_mono hsub (depth + 1)
      have hCoarseSmall : cmp99ActiveCoarseRegion (M := M)
          (N' := cmp99RegionalLatticeSize M N depth) fineSmall =
          cmp99IteratedLiftActiveRegion (M := M) OmegaSmall depth := by
        simpa [fineSmall] using
          cmp99ActiveCoarseRegion_iteratedLift_succ_eq
            (M := M) OmegaSmall depth
      have hCoarseLarge : cmp99ActiveCoarseRegion (M := M)
          (N' := cmp99RegionalLatticeSize M N depth) fineLarge =
          cmp99IteratedLiftActiveRegion (M := M) OmegaLarge depth := by
        simpa [fineLarge] using
          cmp99ActiveCoarseRegion_iteratedLift_succ_eq
            (M := M) OmegaLarge depth
      let tailSmall : CMP99SourceActiveRegionChain d M
          (cmp99RegionalLatticeSize M N depth)
          (cmp99ActiveCoarseRegion (M := M)
            (N' := cmp99RegionalLatticeSize M N depth) fineSmall) depth :=
        hCoarseSmall.symm ▸
          cmp99SourceIteratedLiftActiveRegionChain (M := M) OmegaSmall depth
      let tailLarge : CMP99SourceActiveRegionChain d M
          (cmp99RegionalLatticeSize M N depth)
          (cmp99ActiveCoarseRegion (M := M)
            (N' := cmp99RegionalLatticeSize M N depth) fineLarge) depth :=
        hCoarseLarge.symm ▸
          cmp99SourceIteratedLiftActiveRegionChain (M := M) OmegaLarge depth
      have hTail : CMP99SourceNestedRegionChains d M tailSmall tailLarge := by
        exact CMP99SourceNestedRegionChains.cast_regions
          hCoarseSmall.symm hCoarseLarge.symm ih
      let builtSmall := CMP99SourceActiveRegionChain.step fineSmall hSmall tailSmall
      let builtLarge := CMP99SourceActiveRegionChain.step fineLarge hLarge tailLarge
      have hbSmall : builtSmall =
          cmp99SourceIteratedLiftActiveRegionChain (M := M) OmegaSmall
            (depth + 1) := by
        dsimp [builtSmall, cmp99SourceIteratedLiftActiveRegionChain, fineSmall,
          tailSmall]
        congr 1
        apply eq_of_heq
        exact eqRec_heq_iff_heq.mpr (cast_heq _ _).symm
      have hbLarge : builtLarge =
          cmp99SourceIteratedLiftActiveRegionChain (M := M) OmegaLarge
            (depth + 1) := by
        dsimp [builtLarge, cmp99SourceIteratedLiftActiveRegionChain, fineLarge,
          tailLarge]
        congr 1
        apply eq_of_heq
        exact eqRec_heq_iff_heq.mpr (cast_heq _ _).symm
      rw [← hbSmall, ← hbLarge]
      exact CMP99SourceNestedRegionChains.step fineSmall fineLarge hSmall hLarge
        hFine tailSmall tailLarge hTail

set_option maxHeartbeats 1000000 in
/-- Every typed nested source chain intertwines its recursively generated
counting-Hilbert masses. -/
theorem CMP99SourceNestedRegionChains.generatedCountingMass_transition
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
      let R := cmp99NestedActiveRegionRestriction (g := SUNLieCoord Nc)
        OmegaSmall OmegaLarge
      R.comp (regionsLarge.generatedCountingMass hd hM rho spacing epsilon
          background chain fineSmall) =
        (regionsSmall.generatedCountingMass hd hM rho spacing epsilon
          background chain fineSmall).comp R := by
  letI : NeZero N := regionsSmall.neZero
  induction H with
  | stop OmegaSmall OmegaLarge hsub =>
      intro spacing epsilon background chain fineSmall
      change (cmp99NestedActiveRegionRestriction (g := SUNLieCoord Nc)
          OmegaSmall OmegaLarge).comp (ContinuousLinearMap.id ℝ _) =
        (ContinuousLinearMap.id ℝ _).comp
          (cmp99NestedActiveRegionRestriction (g := SUNLieCoord Nc)
            OmegaSmall OmegaLarge)
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
        simpa [ScaleSmall,
          CMP99SourceNormalizedRegionalScale.ofFineSmall,
          CMP99SourceRegionalScale.ofFineSmall] using
          norm_cmp99SourceRegionalScaleDataOfFineSmall_nextBackground_sub_one_le
            hd hM OmegaSmall background
            (cmp99SourceBlockAverageWeight M d) epsilon
            chain.epsilon_nonneg chain.head_noWinding chain.head_logSmall
            fineSmall e
      let Qsmall := cmp99SourceTransportedBlockAverageCLM OmegaSmall
        (cmp99SourceWeightedPhysicalTransport rho background)
      let Qlarge := cmp99SourceTransportedBlockAverageCLM OmegaLarge
        (cmp99SourceWeightedPhysicalTransport rho background)
      let Rfine := cmp99NestedActiveRegionRestriction (g := SUNLieCoord Nc)
        OmegaSmall OmegaLarge
      let Rcoarse := cmp99NestedActiveRegionRestriction (g := SUNLieCoord Nc)
        (cmp99ActiveCoarseRegion (M := M) (N' := N) OmegaSmall)
        (cmp99ActiveCoarseRegion (M := M) (N' := N) OmegaLarge)
      have hQ : Qsmall.comp Rfine = Rcoarse.comp Qlarge :=
        cmp99SourceTransportedBlockAverage_nested_transition
          OmegaSmall OmegaLarge hsub
          (cmp99SourceWeightedPhysicalTransport rho background)
      have hQstar : Rfine.comp Qlarge.adjoint =
          Qsmall.adjoint.comp Rcoarse :=
        cmp99SourceTransportedBlockAverage_adjoint_nested_transition
          OmegaSmall OmegaLarge hSmall hLarge hsub
          (cmp99SourceWeightedPhysicalTransport rho background)
      have hTail := ih ((M : ℝ) * spacing)
        (cmp99SourceUbarNextFineRadius d M epsilon)
        ScaleSmall.toSourceScale.data.nextBackground chain.tail nextSmall
      have hTail' :
          Rcoarse.comp
              (tailLarge.generatedCountingMass hd hM rho
                ((M : ℝ) * spacing)
                (cmp99SourceUbarNextFineRadius d M epsilon)
                ScaleLarge.toSourceScale.data.nextBackground chain.tail
                nextSmall) =
            (tailSmall.generatedCountingMass hd hM rho
              ((M : ℝ) * spacing)
              (cmp99SourceUbarNextFineRadius d M epsilon)
              ScaleSmall.toSourceScale.data.nextBackground chain.tail
              nextSmall).comp Rcoarse := by
        simpa [Rcoarse, ScaleSmall, ScaleLarge,
          CMP99SourceNormalizedRegionalScale.ofFineSmall,
          CMP99SourceRegionalScale.ofFineSmall] using hTail
      have hStep := cmp99NestedComposedMass_transition
        Qlarge Qsmall
        (tailLarge.generatedCountingMass hd hM rho
          ((M : ℝ) * spacing)
          (cmp99SourceUbarNextFineRadius d M epsilon)
          ScaleLarge.toSourceScale.data.nextBackground chain.tail nextSmall)
        (tailSmall.generatedCountingMass hd hM rho
          ((M : ℝ) * spacing)
          (cmp99SourceUbarNextFineRadius d M epsilon)
          ScaleSmall.toSourceScale.data.nextBackground chain.tail nextSmall)
        Rfine Rcoarse hQ hQstar hTail'
      simpa [CMP99SourceActiveRegionChain.generatedCountingMass,
        Qsmall, Qlarge, Rfine, ScaleSmall, ScaleLarge] using hStep

/-- The generated counting masses of canonical iterated lifts commute exactly
with restriction between any two nested source regions. -/
theorem cmp99SourceIteratedLift_generatedCountingMass_transition
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
    let R := cmp99NestedActiveRegionRestriction (g := SUNLieCoord Nc)
      (cmp99IteratedLiftActiveRegion (M := M) OmegaSmall depth)
      (cmp99IteratedLiftActiveRegion (M := M) OmegaLarge depth)
    R.comp (regionsLarge.generatedCountingMass hd hM rho spacing epsilon
        background chain fineSmall) =
      (regionsSmall.generatedCountingMass hd hM rho spacing epsilon
        background chain fineSmall).comp R := by
  exact (cmp99SourceIteratedLift_nestedRegionChains
    (M := M) hsub depth).generatedCountingMass_transition
      hd hM rho spacing epsilon background chain fineSmall

/-- C3 mass core: the actual generated `Q'^*Q'` masses commute with the
canonical restriction between nested iterated source regions. -/
theorem cmp99SourceIteratedLift_QprimeMass_transition
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
    let R := cmp99NestedActiveRegionRestriction (g := SUNLieCoord Nc)
      (cmp99IteratedLiftActiveRegion (M := M) OmegaSmall depth)
      (cmp99IteratedLiftActiveRegion (M := M) OmegaLarge depth)
    R.comp (Tlarge.Qprime.adjoint.comp Tlarge.Qprime) =
      (Tsmall.Qprime.adjoint.comp Tsmall.Qprime).comp R := by
  let regionsSmall := cmp99SourceIteratedLiftActiveRegionChain
    (M := M) OmegaSmall depth
  let regionsLarge := cmp99SourceIteratedLiftActiveRegionChain
    (M := M) OmegaLarge depth
  simp only
  rw [← regionsLarge.generatedCountingMass_eq_QprimeMass hd hM rho spacing
      epsilon background chain fineSmall,
    ← regionsSmall.generatedCountingMass_eq_QprimeMass hd hM rho spacing
      epsilon background chain fineSmall]
  exact cmp99SourceIteratedLift_generatedCountingMass_transition hsub hd hM rho
    depth spacing epsilon background chain fineSmall

namespace CMP99SourceDependentOmegaGeometry

set_option maxHeartbeats 1000000 in
/-- C3 for the literal consecutive CMP99 domains: the complete generated
`Q'^*Q'` mass cancels exactly under the physical transition restriction. -/
theorem generatedQprimeMass_transition
    {Q j : ℕ} [NeZero Q]
    {ScaleSite : Fin (j + 2) → Type*}
    [∀ r, DecidableEq (ScaleSite r)]
    {Scaled : CMP99SourceScaledStratification
      (FinBox 4 (2 * Q)) (j + 2) ScaleSite}
    {cell : FinBox 4 Q}
    {dist : FinBox 4 (2 * Q) → FinBox 4 (2 * Q) → ℕ}
    {gap : Fin (j + 1) → ℕ}
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
        (depth + 1)).comp (Tlarge.Qprime.adjoint.comp Tlarge.Qprime) =
      (Tsmall.Qprime.adjoint.comp Tsmall.Qprime).comp
        (D.generatedTransitionRestriction (M := M) (Nc := Nc) hpi5 r
          (depth + 1)) := by
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
    operatorRegion] using
    (cmp99SourceIteratedLift_QprimeMass_transition
      (M := M) (Nc := Nc) hsub (by norm_num) hM
      (matrixSUNAdjointModel Nc) (depth + 1) spacing epsilon background
      budget.toRadiusChain fineSmall)

set_option maxHeartbeats 1000000 in
/-- C3 terminal endpoint: the complete generated adjoint mass cancels from
the physical rectangular precision defect, so the defect is exactly the
Dirichlet covariant-Laplacian transition defect. -/
theorem generatedPhysicalPrecisionDefect_eq_laplacianDefect
    {Q j : ℕ} [NeZero Q]
    {ScaleSite : Fin (j + 2) → Type*}
    [∀ r, DecidableEq (ScaleSite r)]
    {Scaled : CMP99SourceScaledStratification
      (FinBox 4 (2 * Q)) (j + 2) ScaleSite}
    {cell : FinBox 4 Q}
    {dist : FinBox 4 (2 * Q) → FinBox 4 (2 * Q) → ℕ}
    {gap : Fin (j + 1) → ℕ}
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
    cmp99TypedPrecisionDefect
        (cmp99SourceGeneratedPhysicalPrecision (by norm_num) hM
          (D.operatorCoarseRegion hpi5 (cmp99OmegaTransitionIndex r))
          depth spacing epsilon background budget fineSmall)
        (cmp99SourceGeneratedPhysicalPrecision (by norm_num) hM
          (D.operatorCoarseRegion hpi5 (cmp99OmegaTransitionNextIndex r))
          depth spacing epsilon background budget fineSmall)
        (D.generatedTransitionRestriction (M := M) (Nc := Nc) hpi5 r
          (depth + 1)) =
      cmp99TypedPrecisionDefect
        (cmp99ActiveRegionSourceCovariantLaplacian
          (D.operatorRegion (M := M) hpi5
            (cmp99OmegaTransitionIndex r) (depth + 1))
          (matrixSUNAdjointModel Nc) background spacing)
        (cmp99ActiveRegionSourceCovariantLaplacian
          (D.operatorRegion (M := M) hpi5
            (cmp99OmegaTransitionNextIndex r) (depth + 1))
          (matrixSUNAdjointModel Nc) background spacing)
        (D.generatedTransitionRestriction (M := M) (Nc := Nc) hpi5 r
          (depth + 1)) := by
  rw [cmp99SourceGeneratedPhysicalPrecision,
    cmp99SourceGeneratedPhysicalPrecision,
    cmp99SourceGaugePrecision, cmp99SourceGaugePrecision]
  exact cmp99TypedPrecisionDefect_add_mass_eq _ _ _ _ _ _
    (D.generatedQprimeMass_transition (M := M) (Nc := Nc) hpi5 r hM depth
      spacing epsilon background budget fineSmall)

end CMP99SourceDependentOmegaGeometry

end

end YangMills.RG
