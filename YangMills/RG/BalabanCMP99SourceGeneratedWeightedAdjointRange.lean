/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceGeneratedMassRange
import YangMills.RG.BalabanCMP99SourceGeneratedTerminalCoordinates
import YangMills.RG.FinitePiLpTypedKernel

/-!
# Exact terminal-block support of the generated weighted adjoint

The printed multiscale synthesis `(Q'_j)^*` is the reverse composition of
the literal one-step block syntheses.  Consequently a terminal coordinate
probe is supported exactly on the fine sites having that terminal owner.
This file exposes that rectangular support before any operator-norm bound is
used.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {d M N Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero N] [NeZero Nc]

/-- The terminal site reached by a fine site along a typed physical region
chain. -/
def CMP99SourceActiveRegionChain.terminalSiteOfFine
    {N depth : ℕ} {Omega : ActiveGaugeRegion d N}
    (regions : CMP99SourceActiveRegionChain d M N Omega depth) :
    ActiveGaugeRegion.Site Omega → regions.terminalSite := by
  induction regions with
  | stop Omega => exact id
  | @step N' depth _ Omega hOmega tail ih =>
      exact fun x => ih (cmp99ActiveCoarseSiteOfFine Omega hOmega x)

omit [NeZero d] in
@[simp] theorem CMP99SourceActiveRegionChain.terminalSiteOfFine_stop
    (Omega : ActiveGaugeRegion d N) (x : ActiveGaugeRegion.Site Omega) :
    (CMP99SourceActiveRegionChain.stop (M := M) Omega).terminalSiteOfFine x = x :=
  rfl

omit [NeZero d] in
theorem CMP99SourceActiveRegionChain.terminalSiteOfFine_step
    {N' depth : ℕ} [NeZero N']
    (Omega : ActiveGaugeRegion d (M * N')) (hOmega : Omega.BlockSaturated)
    (tail : CMP99SourceActiveRegionChain d M N'
      (cmp99ActiveCoarseRegion (M := M) (N' := N') Omega) depth)
    (x : ActiveGaugeRegion.Site Omega) :
    (CMP99SourceActiveRegionChain.step Omega hOmega tail).terminalSiteOfFine x =
      tail.terminalSiteOfFine
        (cmp99ActiveCoarseSiteOfFine Omega hOmega x) := rfl

omit [NeZero d] in
/-- The recursive terminal-block relation is equality of terminal owners. -/
theorem CMP99SourceActiveRegionChain.sameTerminalBlock_iff_terminalSiteOfFine_eq
    {N depth : ℕ} {Omega : ActiveGaugeRegion d N}
    (regions : CMP99SourceActiveRegionChain d M N Omega depth)
    (source target : ActiveGaugeRegion.Site Omega) :
    regions.SameTerminalBlock source target ↔
      regions.terminalSiteOfFine source = regions.terminalSiteOfFine target := by
  induction regions with
  | stop Omega => rfl
  | @step N' depth _ Omega hOmega tail ih =>
      exact ih _ _

omit [NeZero d] in
/-- The recursively defined terminal Hilbert carrier is definitionally the
field indexed by the recursively defined terminal site type. -/
theorem CMP99SourceActiveRegionChain.terminalHilbertSpace_carrier_eq
    {N depth : ℕ} {Omega : ActiveGaugeRegion d N}
    (regions : CMP99SourceActiveRegionChain d M N Omega depth) :
    (regions.terminalHilbertSpace Nc).carrier =
      PiLp 2 (fun _ : regions.terminalSite => SUNLieCoord Nc) := by
  induction regions with
  | stop Omega => rfl
  | step Omega hOmega tail ih => exact ih

/-- The explicit Hilbert bundle on the terminal coordinate type. -/
noncomputable def CMP99SourceActiveRegionChain.terminalCoordinateHilbertSpace
    {N depth : ℕ} {Omega : ActiveGaugeRegion d N}
    (regions : CMP99SourceActiveRegionChain d M N Omega depth) :
    CMP99SourceWeightedTowerHilbertSpace where
  carrier := PiLp 2 (fun _ : regions.terminalSite => SUNLieCoord Nc)

omit [NeZero d] in
/-- The recursively stored terminal Hilbert bundle is the explicit terminal
coordinate bundle, including all analytic instances. -/
theorem CMP99SourceActiveRegionChain.terminalHilbertSpace_eq_coordinate
    {N depth : ℕ} {Omega : ActiveGaugeRegion d N}
    (regions : CMP99SourceActiveRegionChain d M N Omega depth) :
    regions.terminalHilbertSpace Nc =
      regions.terminalCoordinateHilbertSpace (Nc := Nc) := by
  induction regions with
  | stop Omega => rfl
  | step Omega hOmega tail ih =>
      change tail.terminalHilbertSpace Nc =
        tail.terminalCoordinateHilbertSpace (Nc := Nc)
      exact ih

/-- The generated weighted adjoint with its terminal coordinate type exposed
as the physical `PiLp` field indexed by `terminalSite`.  Both transports are
equalities of complete Hilbert bundles, so no condition number is introduced.
-/
noncomputable def CMP99SourceActiveRegionChain.physicalWeightedAdjoint
    {N depth : ℕ} {Omega : ActiveGaugeRegion d N}
    (regions : CMP99SourceActiveRegionChain d M N Omega depth)
    (hd : 2 ≤ d) (hM : 2 ≤ M) (rho : SUNAdjointModel Nc) :
    letI : NeZero N := regions.neZero
    (spacing epsilon : ℝ) → (background : GaugeConfig d N (SUN Nc)) →
    (chain : CMP99SourceUbarRadiusChain d M Nc depth epsilon) →
    (fineSmall : ∀ e : ConcreteEdge d N,
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon) →
    PiLp 2 (fun _ : regions.terminalSite => SUNLieCoord Nc) →L[ℝ]
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
      exact (cmp99SourceTransportedBlockWeightedAdjointCLM Omega hOmega
        (cmp99SourceWeightedPhysicalTransport rho background)).comp
          (ih ((M : ℝ) * spacing)
            (cmp99SourceUbarNextFineRadius d M epsilon)
            Scale.toSourceScale.data.nextBackground chain.tail nextSmall)

/-- The original bundled generated weighted adjoint, transported only to
expose its terminal physical coordinate type. -/
noncomputable def CMP99SourceActiveRegionChain.transportedWeightedAdjoint
    {N depth : ℕ} {Omega : ActiveGaugeRegion d N}
    (regions : CMP99SourceActiveRegionChain d M N Omega depth)
    (hd : 2 ≤ d) (hM : 2 ≤ M) (rho : SUNAdjointModel Nc) :
    letI : NeZero N := regions.neZero
    (spacing epsilon : ℝ) → (background : GaugeConfig d N (SUN Nc)) →
    (chain : CMP99SourceUbarRadiusChain d M Nc depth epsilon) →
    (fineSmall : ∀ e : ConcreteEdge d N,
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon) →
    PiLp 2 (fun _ : regions.terminalSite => SUNLieCoord Nc) →L[ℝ]
      ActiveGaugeZeroCochain Omega (SUNLieCoord Nc) := by
  letI : NeZero N := regions.neZero
  intro spacing epsilon background chain fineSmall
  let T := regions.weightedQprimeTower hd hM rho spacing epsilon background
    chain fineSmall
  let hT : T.TerminalSpace = regions.terminalHilbertSpace Nc :=
    regions.weightedQprimeTower_terminalSpace_eq hd hM rho spacing epsilon
      background chain fineSmall
  let hCoord : regions.terminalHilbertSpace Nc =
      regions.terminalCoordinateHilbertSpace (Nc := Nc) :=
    regions.terminalHilbertSpace_eq_coordinate
  exact cmp99SourceTerminalCLMTransport
    (E := T.TerminalSpace)
    (F := cmp99SourcePhysicalTerminalHilbertSpace Nc Omega)
    (E' := regions.terminalCoordinateHilbertSpace (Nc := Nc))
    (F' := cmp99SourcePhysicalTerminalHilbertSpace Nc Omega)
    (hT.trans hCoord) rfl T.weightedAdjoint

/-- The recursive physical synthesis is exactly the original generated
weighted adjoint after the canonical terminal-coordinate transport. -/
theorem CMP99SourceActiveRegionChain.physicalWeightedAdjoint_eq_transported
    {N depth : ℕ} {Omega : ActiveGaugeRegion d N}
    (regions : CMP99SourceActiveRegionChain d M N Omega depth)
    (hd : 2 ≤ d) (hM : 2 ≤ M) (rho : SUNAdjointModel Nc) :
    letI : NeZero N := regions.neZero
    ∀ (spacing epsilon : ℝ) (background : GaugeConfig d N (SUN Nc))
      (chain : CMP99SourceUbarRadiusChain d M Nc depth epsilon)
      (fineSmall : ∀ e : ConcreteEdge d N,
        ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon),
      regions.physicalWeightedAdjoint hd hM rho spacing epsilon background
          chain fineSmall =
        regions.transportedWeightedAdjoint hd hM rho spacing epsilon background
          chain fineSmall := by
  letI : NeZero N := regions.neZero
  induction regions with
  | stop Omega =>
      intro spacing epsilon background chain fineSmall
      rfl
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
      have htail := ih ((M : ℝ) * spacing)
        (cmp99SourceUbarNextFineRadius d M epsilon)
        Scale.toSourceScale.data.nextBackground chain.tail nextSmall
      change (cmp99SourceTransportedBlockWeightedAdjointCLM Omega hOmega
          (cmp99SourceWeightedPhysicalTransport rho background)).comp
            (tail.physicalWeightedAdjoint hd hM rho ((M : ℝ) * spacing)
              (cmp99SourceUbarNextFineRadius d M epsilon)
              Scale.toSourceScale.data.nextBackground chain.tail nextSmall) = _
      rw [htail]
      let tailT := tail.weightedQprimeTower hd hM rho ((M : ℝ) * spacing)
        (cmp99SourceUbarNextFineRadius d M epsilon)
        Scale.toSourceScale.data.nextBackground chain.tail nextSmall
      let hTailT : tailT.TerminalSpace = tail.terminalHilbertSpace Nc :=
        tail.weightedQprimeTower_terminalSpace_eq hd hM rho
          ((M : ℝ) * spacing) (cmp99SourceUbarNextFineRadius d M epsilon)
          Scale.toSourceScale.data.nextBackground chain.tail nextSmall
      let hTailCoord : tail.terminalHilbertSpace Nc =
          tail.terminalCoordinateHilbertSpace (Nc := Nc) :=
        tail.terminalHilbertSpace_eq_coordinate
      let Head := cmp99SourceTransportedBlockWeightedAdjointCLM Omega hOmega
        (cmp99SourceWeightedPhysicalTransport rho background)
      have hcomp := cmp99SourceTerminalCLMTransport_comp
        (E := tailT.TerminalSpace)
        (F := cmp99SourcePhysicalTerminalHilbertSpace Nc
          (cmp99ActiveCoarseRegion (M := M) (N' := N') Omega))
        (G := cmp99SourcePhysicalTerminalHilbertSpace Nc Omega)
        (E' := tail.terminalCoordinateHilbertSpace (Nc := Nc))
        (F' := cmp99SourcePhysicalTerminalHilbertSpace Nc
          (cmp99ActiveCoarseRegion (M := M) (N' := N') Omega))
        (G' := cmp99SourcePhysicalTerminalHilbertSpace Nc Omega)
        (hTailT.trans hTailCoord) rfl rfl Head tailT.weightedAdjoint
      simpa [transportedWeightedAdjoint, tailT, Head] using hcomp

/-- Exposing terminal coordinates does not change the operator norm of the
literal generated weighted adjoint. -/
theorem CMP99SourceActiveRegionChain.norm_physicalWeightedAdjoint
    {N depth : ℕ} {Omega : ActiveGaugeRegion d N}
    (regions : CMP99SourceActiveRegionChain d M N Omega depth)
    (hd : 2 ≤ d) (hM : 2 ≤ M) (rho : SUNAdjointModel Nc) :
    letI : NeZero N := regions.neZero
    ∀ (spacing epsilon : ℝ) (background : GaugeConfig d N (SUN Nc))
      (chain : CMP99SourceUbarRadiusChain d M Nc depth epsilon)
      (fineSmall : ∀ e : ConcreteEdge d N,
        ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon),
      ‖regions.physicalWeightedAdjoint hd hM rho spacing epsilon background
          chain fineSmall‖ =
        ‖(regions.weightedQprimeTower hd hM rho spacing epsilon background
          chain fineSmall).weightedAdjoint‖ := by
  letI : NeZero N := regions.neZero
  intro spacing epsilon background chain fineSmall
  rw [regions.physicalWeightedAdjoint_eq_transported hd hM rho spacing epsilon
    background chain fineSmall]
  unfold transportedWeightedAdjoint
  dsimp only
  exact norm_cmp99SourceTerminalCLMTransport _ _ _

/-- A terminal coordinate probe synthesizes to zero at every fine site with
a different terminal owner. -/
theorem CMP99SourceActiveRegionChain.physicalWeightedAdjoint_single_apply_eq_zero
    {N depth : ℕ} {Omega : ActiveGaugeRegion d N}
    (regions : CMP99SourceActiveRegionChain d M N Omega depth)
    (hd : 2 ≤ d) (hM : 2 ≤ M) (rho : SUNAdjointModel Nc) :
    letI : NeZero N := regions.neZero
    ∀ (spacing epsilon : ℝ) (background : GaugeConfig d N (SUN Nc))
      (chain : CMP99SourceUbarRadiusChain d M Nc depth epsilon)
      (fineSmall : ∀ e : ConcreteEdge d N,
        ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
      (source : regions.terminalSite) (target : ActiveGaugeRegion.Site Omega)
      (v : SUNLieCoord Nc),
      regions.terminalSiteOfFine target ≠ source →
      regions.physicalWeightedAdjoint hd hM rho spacing epsilon background
          chain fineSmall (singleFinitePiLp source v) target = 0 := by
  letI : NeZero N := regions.neZero
  induction regions with
  | stop Omega =>
      intro spacing epsilon background chain fineSmall source target v hne
      change singleFinitePiLp source v target = 0
      exact singleFinitePiLp_of_ne v hne
  | @step N' depth _ Omega hOmega tail ih =>
      intro spacing epsilon background chain fineSmall source target v hne
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
      have htail := ih ((M : ℝ) * spacing)
        (cmp99SourceUbarNextFineRadius d M epsilon)
        Scale.toSourceScale.data.nextBackground chain.tail nextSmall source
        (cmp99ActiveCoarseSiteOfFine Omega hOmega target) v hne
      change cmp99SourceTransportedBlockWeightedAdjointCLM Omega hOmega
          (cmp99SourceWeightedPhysicalTransport rho background)
          (tail.physicalWeightedAdjoint hd hM rho ((M : ℝ) * spacing)
            (cmp99SourceUbarNextFineRadius d M epsilon)
            Scale.toSourceScale.data.nextBackground chain.tail nextSmall
            (singleFinitePiLp source v)) target = 0
      rw [cmp99SourceTransportedBlockWeightedAdjointCLM,
        cmp99TransportedBlockSynthesisCLM_apply]
      let targetCoarse : ActiveGaugeRegion.Site
          (cmp99ActiveCoarseRegion (M := M) (N' := N') Omega) :=
        ⟨blockSite M N' target.1,
          (mem_cmp99ActiveCoarseRegion_sites_iff
            (M := M) (N' := N') Omega (blockSite M N' target.1)).2
              (hOmega target.1 target.2)⟩
      have htargetCoarse : targetCoarse =
          cmp99ActiveCoarseSiteOfFine Omega hOmega target := by
        apply Subtype.ext
        rfl
      have htail' :
          (tail.physicalWeightedAdjoint hd hM rho ((M : ℝ) * spacing)
            (cmp99SourceUbarNextFineRadius d M epsilon)
            Scale.toSourceScale.data.nextBackground chain.tail nextSmall
            (singleFinitePiLp source v)) targetCoarse = 0 := by
        rw [htargetCoarse]
        exact htail
      rw [show (⟨blockSite M N' target.1,
          (mem_cmp99ActiveCoarseRegion_sites_iff
            (M := M) (N' := N') Omega (blockSite M N' target.1)).2
              (hOmega target.1 target.2)⟩ : ActiveGaugeRegion.Site
            (cmp99ActiveCoarseRegion (M := M) (N' := N') Omega)) =
          targetCoarse by rfl]
      rw [htail', map_zero, smul_zero]

/-- Canonical fine representative of a terminal site of an arbitrary typed
source chain.  At each reverse step it chooses the lower corner of the
complete owner block. -/
def CMP99SourceActiveRegionChain.terminalRepresentative
    {N depth : ℕ} {Omega : ActiveGaugeRegion d N}
    (regions : CMP99SourceActiveRegionChain d M N Omega depth) :
    regions.terminalSite → ActiveGaugeRegion.Site Omega := by
  induction regions with
  | stop Omega => exact id
  | @step N' depth _ Omega hOmega tail ih =>
      intro source
      let coarse := ih source
      exact ⟨blockBasepoint M N' coarse.1,
        (mem_cmp99ActiveCoarseRegion_sites_iff
          (M := M) (N' := N') Omega coarse.1).mp coarse.2
            ((mem_blockOf M N' coarse.1 (blockBasepoint M N' coarse.1)).2
              (blockSite_blockBasepoint M N' coarse.1))⟩

omit [NeZero d] in
/-- The chosen fine representative has exactly the requested terminal owner. -/
@[simp] theorem CMP99SourceActiveRegionChain.terminalSiteOfFine_representative
    {N depth : ℕ} {Omega : ActiveGaugeRegion d N}
    (regions : CMP99SourceActiveRegionChain d M N Omega depth)
    (source : regions.terminalSite) :
    regions.terminalSiteOfFine (regions.terminalRepresentative source) =
      source := by
  induction regions with
  | stop Omega => rfl
  | @step N' depth _ Omega hOmega tail ih =>
      change tail.terminalSiteOfFine
          (cmp99ActiveCoarseSiteOfFine Omega hOmega
            ((CMP99SourceActiveRegionChain.step Omega hOmega tail
              |>.terminalRepresentative) source)) = source
      have hcoarse : cmp99ActiveCoarseSiteOfFine Omega hOmega
          ((CMP99SourceActiveRegionChain.step Omega hOmega tail
            |>.terminalRepresentative) source) =
          tail.terminalRepresentative source := by
        apply Subtype.ext
        exact blockSite_blockBasepoint M N'
          (tail.terminalRepresentative source).1
      rw [hcoarse]
      exact ih source

omit [NeZero d] in
/-- A distance beyond the diameter of one terminal block forces different
terminal owners.  This is the purely geometric input to the rectangular
finite-range theorem. -/
theorem CMP99SourceActiveRegionChain.terminalSiteOfFine_ne_of_dist_gt
    {N depth : ℕ} {Omega : ActiveGaugeRegion d N}
    (regions : CMP99SourceActiveRegionChain d M N Omega depth)
    (dist : ActiveGaugeRegion.Site Omega →
      ActiveGaugeRegion.Site Omega → ℕ) (R : ℕ)
    (hdiameter : ∀ source target,
      regions.SameTerminalBlock source target → dist target source ≤ R)
    (source : regions.terminalSite) (target : ActiveGaugeRegion.Site Omega)
    (hfar : R < dist target (regions.terminalRepresentative source)) :
    regions.terminalSiteOfFine target ≠ source := by
  intro howner
  have hsame : regions.SameTerminalBlock
      (regions.terminalRepresentative source) target :=
    (regions.sameTerminalBlock_iff_terminalSiteOfFine_eq _ _).2 <| by
      rw [regions.terminalSiteOfFine_representative, howner]
  exact (Nat.not_lt_of_ge (hdiameter _ _ hsame)) hfar

/-- The canonical lifted source chain has terminal-block diameter
`M^depth - 1` in the native fine-lattice metric. -/
theorem cmp99SourceIteratedLift_terminalBlock_diameter
    (Omega : ActiveGaugeRegion d N) (depth : ℕ)
    (source target : ActiveGaugeRegion.Site
      (cmp99IteratedLiftActiveRegion (M := M) Omega depth))
    (hsame : (cmp99SourceIteratedLiftActiveRegionChain
      (M := M) Omega depth).SameTerminalBlock source target) :
    finBoxDist target.1 source.1 ≤ M ^ depth - 1 := by
  apply finBoxDist_le_of_same_generatedTerminalBlock (M := M) depth
  exact ((cmp99SourceIteratedLift_sameTerminalBlock_iff
    (M := M) Omega depth source target).1 hsame).symm

set_option maxHeartbeats 4000000 in
/-- The canonical generated weighted adjoint has the explicit rectangular
range `M^depth - 1`, measured from the canonical representative of each
terminal source coordinate. -/
theorem cmp99SourceIteratedLift_physicalWeightedAdjoint_finiteRange
    (Omega : ActiveGaugeRegion d N) (depth : ℕ)
    (hd : 2 ≤ d) (hM : 2 ≤ M) (rho : SUNAdjointModel Nc)
    (spacing epsilon : ℝ)
    (background : GaugeConfig d (cmp99RegionalLatticeSize M N depth) (SUN Nc))
    (chain : CMP99SourceUbarRadiusChain d M Nc depth epsilon)
    (fineSmall : ∀ e : ConcreteEdge d
      (cmp99RegionalLatticeSize M N depth),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon) :
    let regions := cmp99SourceIteratedLiftActiveRegionChain
      (M := M) Omega depth
    FinitePiLpTypedFiniteRange
      (regions.physicalWeightedAdjoint hd hM rho spacing epsilon background
        chain fineSmall)
      (fun target source => finBoxDist target.1
        (regions.terminalRepresentative source).1)
      (M ^ depth - 1) := by
  dsimp only
  let regions := cmp99SourceIteratedLiftActiveRegionChain
    (M := M) Omega depth
  intro source target v hfar
  apply regions.physicalWeightedAdjoint_single_apply_eq_zero
    hd hM rho spacing epsilon background chain fineSmall source target v
  exact regions.terminalSiteOfFine_ne_of_dist_gt
    (fun x y => finBoxDist x.1 y.1) (M ^ depth - 1)
    (cmp99SourceIteratedLift_terminalBlock_diameter
      (M := M) Omega depth) source target hfar

end
end YangMills.RG
