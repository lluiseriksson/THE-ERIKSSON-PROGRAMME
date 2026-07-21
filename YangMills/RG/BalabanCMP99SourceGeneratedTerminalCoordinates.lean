/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceGeneratedPoincareQprime

/-!
# Terminal coordinates of the generated CMP99 source tower

The dependent source chain ends on a site type determined by its literal
recursive endpoint.  This module records that type and proves that the
canonical iterated lift ends exactly on the original physical source region.
Consequently the bundled terminal carrier of the printed `Q'_j` tower has a
canonical physical coordinate type, without a caller-supplied equivalence.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {d M N Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero N] [NeZero Nc]

/-- The site type at the literal endpoint of a typed source region chain. -/
def CMP99SourceActiveRegionChain.terminalSite
    {N depth : ℕ} {Omega : ActiveGaugeRegion d N}
    (regions : CMP99SourceActiveRegionChain d M N Omega depth) : Type := by
  induction regions with
  | stop Omega => exact ActiveGaugeRegion.Site Omega
  | step Omega hOmega tail ih => exact ih

noncomputable instance CMP99SourceActiveRegionChain.terminalSiteDecidableEq
    {N depth : ℕ} {Omega : ActiveGaugeRegion d N}
    (regions : CMP99SourceActiveRegionChain d M N Omega depth) :
    DecidableEq regions.terminalSite := by
  induction regions with
  | stop Omega =>
      change DecidableEq (ActiveGaugeRegion.Site Omega)
      exact inferInstance
  | step Omega hOmega tail ih => exact ih

noncomputable instance CMP99SourceActiveRegionChain.terminalSiteFintype
    {N depth : ℕ} {Omega : ActiveGaugeRegion d N}
    (regions : CMP99SourceActiveRegionChain d M N Omega depth) :
    Fintype regions.terminalSite := by
  induction regions with
  | stop Omega =>
      change Fintype (ActiveGaugeRegion.Site Omega)
      exact inferInstance
  | step Omega hOmega tail ih => exact ih

/-- The physical Hilbert bundle carried by one active source region. -/
noncomputable def cmp99SourcePhysicalTerminalHilbertSpace
    (Nc : ℕ) [NeZero Nc] (Omega : ActiveGaugeRegion d N) :
    CMP99SourceWeightedTowerHilbertSpace where
  carrier := PiLp 2 (fun _ : ActiveGaugeRegion.Site Omega => SUNLieCoord Nc)

/-- The exact endpoint Hilbert bundle of a typed source region chain. -/
noncomputable def CMP99SourceActiveRegionChain.terminalHilbertSpace
    (Nc : ℕ) [NeZero Nc]
    {N depth : ℕ} {Omega : ActiveGaugeRegion d N}
    (regions : CMP99SourceActiveRegionChain d M N Omega depth) :
    CMP99SourceWeightedTowerHilbertSpace := by
  induction regions with
  | stop Omega => exact cmp99SourcePhysicalTerminalHilbertSpace Nc Omega
  | step Omega hOmega tail ih => exact ih

omit [NeZero d] in
theorem CMP99SourceActiveRegionChain.terminalHilbertSpace_mpr
    {Omega₁ Omega₂ : ActiveGaugeRegion d N} (h : Omega₁ = Omega₂)
    {depth : ℕ}
    (regions : CMP99SourceActiveRegionChain d M N Omega₂ depth) :
    (Eq.mpr (congrArg
      (fun region => CMP99SourceActiveRegionChain d M N region depth) h)
      regions).terminalHilbertSpace Nc = regions.terminalHilbertSpace Nc := by
  cases h
  rfl

omit [NeZero N] in
theorem CMP99SourceActiveRegionChain.weightedQprimeTower_terminalSpace_eq
    {depth : ℕ} {Omega : ActiveGaugeRegion d N}
    (regions : CMP99SourceActiveRegionChain d M N Omega depth)
    (hd : 2 ≤ d) (hM : 2 ≤ M) (rho : SUNAdjointModel Nc) :
    letI : NeZero N := regions.neZero
    ∀ (spacing epsilon : ℝ) (background : GaugeConfig d N (SUN Nc))
      (chain : CMP99SourceUbarRadiusChain d M Nc depth epsilon)
      (fineSmall : ∀ e : ConcreteEdge d N,
        ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon),
      (regions.weightedQprimeTower hd hM rho spacing epsilon background chain
        fineSmall).TerminalSpace = regions.terminalHilbertSpace Nc := by
  letI : NeZero N := regions.neZero
  induction regions with
  | stop Omega =>
      intro spacing epsilon background chain fineSmall
      rfl
  | @step N' depth _ Omega hOmega tail ih =>
      intro spacing epsilon background chain fineSmall
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
      exact ih ((M : ℝ) * spacing)
        (cmp99SourceUbarNextFineRadius d M epsilon)
        Scale.toSourceScale.data.nextBackground chain.tail nextSmall

omit [NeZero d] [NeZero N] in
theorem CMP99SourceActiveRegionChain.terminalSite_mpr
    {Omega₁ Omega₂ : ActiveGaugeRegion d N} (h : Omega₁ = Omega₂)
    {depth : ℕ}
    (regions : CMP99SourceActiveRegionChain d M N Omega₂ depth) :
    (Eq.mpr (congrArg
      (fun region => CMP99SourceActiveRegionChain d M N region depth) h)
      regions).terminalSite = regions.terminalSite := by
  cases h
  rfl

omit [NeZero N] in
theorem CMP99SourceActiveRegionChain.weightedQprimeTower_terminalCarrier_eq
    {depth : ℕ} {Omega : ActiveGaugeRegion d N}
    (regions : CMP99SourceActiveRegionChain d M N Omega depth)
    (hd : 2 ≤ d) (hM : 2 ≤ M) (rho : SUNAdjointModel Nc) :
    letI : NeZero N := regions.neZero
    ∀ (spacing epsilon : ℝ) (background : GaugeConfig d N (SUN Nc))
      (chain : CMP99SourceUbarRadiusChain d M Nc depth epsilon)
      (fineSmall : ∀ e : ConcreteEdge d N,
        ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon),
      (regions.weightedQprimeTower hd hM rho spacing epsilon background chain
        fineSmall).TerminalSpace.carrier =
        PiLp 2 (fun _ : regions.terminalSite => SUNLieCoord Nc) := by
  letI : NeZero N := regions.neZero
  induction regions with
  | stop Omega =>
      intro spacing epsilon background chain fineSmall
      rfl
  | @step N' depth _ Omega hOmega tail ih =>
      intro spacing epsilon background chain fineSmall
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
      exact ih ((M : ℝ) * spacing)
        (cmp99SourceUbarNextFineRadius d M epsilon)
        Scale.toSourceScale.data.nextBackground chain.tail nextSmall

/-- The canonical iterated source lift ends on the original physical site
type, independently of the proposition used to rewrite each coarse region. -/
theorem cmp99SourceIteratedLiftActiveRegionChain_terminalSite_eq
    (Omega : ActiveGaugeRegion d N) :
    ∀ depth : ℕ,
      (cmp99SourceIteratedLiftActiveRegionChain (M := M) Omega depth
        |>.terminalSite) = ActiveGaugeRegion.Site Omega := by
  intro depth
  induction depth with
  | zero => rfl
  | succ depth ih =>
      simp only [cmp99SourceIteratedLiftActiveRegionChain,
        CMP99SourceActiveRegionChain.terminalSite]
      have hregion := cmp99ActiveCoarseRegion_iteratedLift_succ_eq
        (M := M) Omega depth
      let tail' : CMP99SourceActiveRegionChain d M
          (cmp99RegionalLatticeSize M N depth)
          (cmp99ActiveCoarseRegion
            (M := M) (N' := cmp99RegionalLatticeSize M N depth)
            (cmp99IteratedLiftActiveRegion (M := M) Omega (depth + 1)))
          depth := by
        rw [hregion]
        exact cmp99SourceIteratedLiftActiveRegionChain (M := M) Omega depth
      change tail'.terminalSite = ActiveGaugeRegion.Site Omega
      have hsite : tail'.terminalSite =
          (cmp99SourceIteratedLiftActiveRegionChain (M := M) Omega depth
            |>.terminalSite) := by
        exact CMP99SourceActiveRegionChain.terminalSite_mpr hregion
          (cmp99SourceIteratedLiftActiveRegionChain (M := M) Omega depth)
      rw [hsite]
      exact ih

/-- The canonical chain ends in the complete physical Hilbert bundle on its
original source region, including the stored norm and inner-product
instances. -/
theorem cmp99SourceIteratedLiftActiveRegionChain_terminalHilbertSpace_eq
    (Omega : ActiveGaugeRegion d N) :
    ∀ depth : ℕ,
      (cmp99SourceIteratedLiftActiveRegionChain (M := M) Omega depth
        |>.terminalHilbertSpace Nc) =
      cmp99SourcePhysicalTerminalHilbertSpace Nc Omega := by
  intro depth
  induction depth with
  | zero => rfl
  | succ depth ih =>
      simp only [cmp99SourceIteratedLiftActiveRegionChain,
        CMP99SourceActiveRegionChain.terminalHilbertSpace]
      have hregion := cmp99ActiveCoarseRegion_iteratedLift_succ_eq
        (M := M) Omega depth
      let tail' : CMP99SourceActiveRegionChain d M
          (cmp99RegionalLatticeSize M N depth)
          (cmp99ActiveCoarseRegion
            (M := M) (N' := cmp99RegionalLatticeSize M N depth)
            (cmp99IteratedLiftActiveRegion (M := M) Omega (depth + 1)))
          depth := by
        rw [hregion]
        exact cmp99SourceIteratedLiftActiveRegionChain (M := M) Omega depth
      change tail'.terminalHilbertSpace Nc =
        cmp99SourcePhysicalTerminalHilbertSpace Nc Omega
      have hspace : tail'.terminalHilbertSpace Nc =
          (cmp99SourceIteratedLiftActiveRegionChain (M := M) Omega depth
            |>.terminalHilbertSpace Nc) := by
        exact CMP99SourceActiveRegionChain.terminalHilbertSpace_mpr
          (Nc := Nc) hregion
          (cmp99SourceIteratedLiftActiveRegionChain (M := M) Omega depth)
      rw [hspace]
      exact ih

/-- The bundled terminal Hilbert space of the canonical printed tower is
literally the physical field bundle on the original source region. -/
theorem cmp99SourceIteratedLift_weightedQprimeTower_terminalSpace_eq
    (hd : 2 ≤ d) (hM : 2 ≤ M) (rho : SUNAdjointModel Nc)
    (Omega : ActiveGaugeRegion d N) (depth : ℕ)
    (spacing epsilon : ℝ)
    (background : GaugeConfig d
      (cmp99RegionalLatticeSize M N depth) (SUN Nc))
    (chain : CMP99SourceUbarRadiusChain d M Nc depth epsilon)
    (fineSmall : ∀ e : ConcreteEdge d
      (cmp99RegionalLatticeSize M N depth),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon) :
    (cmp99SourceIteratedLiftActiveRegionChain (M := M) Omega depth
        |>.weightedQprimeTower hd hM rho spacing epsilon background chain
          fineSmall).TerminalSpace =
      cmp99SourcePhysicalTerminalHilbertSpace Nc Omega := by
  let regions := cmp99SourceIteratedLiftActiveRegionChain (M := M) Omega depth
  calc
    (regions.weightedQprimeTower hd hM rho spacing epsilon background chain
        fineSmall).TerminalSpace = regions.terminalHilbertSpace Nc :=
      regions.weightedQprimeTower_terminalSpace_eq hd hM rho spacing epsilon
        background chain fineSmall
    _ = cmp99SourcePhysicalTerminalHilbertSpace Nc Omega :=
      cmp99SourceIteratedLiftActiveRegionChain_terminalHilbertSpace_eq
        (Nc := Nc)
        (M := M) Omega depth

/-- The terminal carrier of the literal canonical `Q'` tower is the field on
the original source region.  No coordinate equivalence is supplied by a
caller. -/
theorem cmp99SourceIteratedLift_weightedQprimeTower_terminalCarrier_eq
    (hd : 2 ≤ d) (hM : 2 ≤ M) (rho : SUNAdjointModel Nc)
    (Omega : ActiveGaugeRegion d N) (depth : ℕ)
    (spacing epsilon : ℝ)
    (background : GaugeConfig d
      (cmp99RegionalLatticeSize M N depth) (SUN Nc))
    (chain : CMP99SourceUbarRadiusChain d M Nc depth epsilon)
    (fineSmall : ∀ e : ConcreteEdge d
      (cmp99RegionalLatticeSize M N depth),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon) :
    (cmp99SourceIteratedLiftActiveRegionChain (M := M) Omega depth
        |>.weightedQprimeTower hd hM rho spacing epsilon background chain
          fineSmall).TerminalSpace.carrier =
      PiLp 2 (fun _ : ActiveGaugeRegion.Site Omega => SUNLieCoord Nc) := by
  let regions := cmp99SourceIteratedLiftActiveRegionChain (M := M) Omega depth
  calc
    (regions.weightedQprimeTower hd hM rho spacing epsilon background chain
        fineSmall).TerminalSpace.carrier =
        PiLp 2 (fun _ : regions.terminalSite => SUNLieCoord Nc) :=
      regions.weightedQprimeTower_terminalCarrier_eq hd hM rho spacing
        epsilon background chain fineSmall
    _ = PiLp 2 (fun _ : ActiveGaugeRegion.Site Omega => SUNLieCoord Nc) := by
      rw [cmp99SourceIteratedLiftActiveRegionChain_terminalSite_eq
        (M := M) Omega depth]

/-- Transport a continuous linear map along equalities of the complete
terminal Hilbert bundles.  Equality of the bundles transports all stored
analytic instances together, unlike equality of their carrier types alone. -/
noncomputable def cmp99SourceTerminalCLMTransport
    {E F E' F' : CMP99SourceWeightedTowerHilbertSpace}
    (hE : E = E') (hF : F = F')
    (C : E.carrier →L[ℝ] F.carrier) : E'.carrier →L[ℝ] F'.carrier := by
  subst E'
  subst F'
  exact C

/-- Transported maps send heterogeneously equal arguments to
heterogeneously equal values.  This is the stable elimination principle for
dependent terminal carriers: it does not require eliminating the concrete
recursive equality which produced the carrier identification. -/
theorem cmp99SourceTerminalCLMTransport_apply_heq
    {E F E' F' : CMP99SourceWeightedTowerHilbertSpace}
    (hE : E = E') (hF : F = F')
    (C : E.carrier →L[ℝ] F.carrier)
    {x : E.carrier} {x' : E'.carrier} (hx : HEq x x') :
    HEq (C x) (cmp99SourceTerminalCLMTransport hE hF C x') := by
  subst E'
  subst F'
  exact congrArg C (eq_of_heq hx) |>.heq

/-- Successive bundle transports compose exactly. -/
theorem cmp99SourceTerminalCLMTransport_trans
    {E F E' F' E'' F'' : CMP99SourceWeightedTowerHilbertSpace}
    (hE : E = E') (hF : F = F') (hE' : E' = E'') (hF' : F' = F'')
    (C : E.carrier →L[ℝ] F.carrier) :
    cmp99SourceTerminalCLMTransport hE' hF'
        (cmp99SourceTerminalCLMTransport hE hF C) =
      cmp99SourceTerminalCLMTransport (hE.trans hE') (hF.trans hF') C := by
  subst E'
  subst F'
  subst E''
  subst F''
  rfl

/-- Bundle transport is isometric on the operator norm. -/
theorem norm_cmp99SourceTerminalCLMTransport
    {E F E' F' : CMP99SourceWeightedTowerHilbertSpace}
    (hE : E = E') (hF : F = F')
    (C : E.carrier →L[ℝ] F.carrier) :
    ‖cmp99SourceTerminalCLMTransport hE hF C‖ = ‖C‖ := by
  subst E'
  subst F'
  rfl

/-- Bundle transport commutes exactly with composition. -/
theorem cmp99SourceTerminalCLMTransport_comp
    {E F G E' F' G' : CMP99SourceWeightedTowerHilbertSpace}
    (hE : E = E') (hF : F = F') (hG : G = G')
    (C : F.carrier →L[ℝ] G.carrier)
    (D : E.carrier →L[ℝ] F.carrier) :
    (cmp99SourceTerminalCLMTransport hF hG C).comp
        (cmp99SourceTerminalCLMTransport hE hF D) =
      cmp99SourceTerminalCLMTransport hE hG (C.comp D) := by
  subst E'
  subst F'
  subst G'
  rfl

/-- Bundle transport commutes exactly with the real scalar action. -/
theorem cmp99SourceTerminalCLMTransport_smul
    {E F E' F' : CMP99SourceWeightedTowerHilbertSpace}
    (hE : E = E') (hF : F = F') (a : ℝ)
    (C : E.carrier →L[ℝ] F.carrier) :
    cmp99SourceTerminalCLMTransport hE hF (a • C) =
      a • cmp99SourceTerminalCLMTransport hE hF C := by
  subst E'
  subst F'
  rfl

/-- Bundle transport commutes exactly with the Hilbert adjoint. -/
theorem cmp99SourceTerminalCLMTransport_adjoint
    {E F E' F' : CMP99SourceWeightedTowerHilbertSpace}
    (hE : E = E') (hF : F = F')
    (C : E.carrier →L[ℝ] F.carrier) :
    cmp99SourceTerminalCLMTransport hF hE C.adjoint =
      (cmp99SourceTerminalCLMTransport hE hF C).adjoint := by
  subst E'
  subst F'
  rfl

/-- Transporting both external legs of a middle operator transports only
the synthesis and analysis maps; the physical middle factors are unchanged. -/
theorem cmp99SourceTerminalCLMTransport_sandwich
    {E E' F : CMP99SourceWeightedTowerHilbertSpace}
    (hE : E = E')
    (Q : F.carrier →L[ℝ] E.carrier)
    (G : F.carrier →L[ℝ] F.carrier)
    (W : E.carrier →L[ℝ] F.carrier) :
    cmp99SourceTerminalCLMTransport hE hE
        (Q.comp (G.comp (G.comp W))) =
      (cmp99SourceTerminalCLMTransport rfl hE Q).comp
        (G.comp (G.comp
          (cmp99SourceTerminalCLMTransport hE rfl W))) := by
  subst E'
  rfl

end
end YangMills.RG
