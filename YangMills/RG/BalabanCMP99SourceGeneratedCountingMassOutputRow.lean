/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceGeneratedCountingMassRow
import YangMills.RG.FinitePiLpTypedFixedOutputWeightedKernel

/-!
# Printed fixed-output rows of the generated CMP99 counting mass

The source-fixed row already proved for `Q'^* Q'` cannot be turned into the
fixed-output row of CMP99 (3.88) by abstract self-adjointness: for a
vector-valued kernel, adjunction transposes each fibre block and does not
preserve a sum of norms on one common test vector.

The physical generated mass has more structure.  Inside one terminal block
every kernel block is the scalar `(M^{-d})^(2*depth)` times a composition of
the literal background isometries; outside that block it is zero.  Hence the
norm of each block is symmetric under exchanging its endpoints.  This file
proves that physical fact by induction and only then reuses the exact
source-row normalization to obtain the printed fixed-output sum.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator RealInnerProductSpace BigOperators

noncomputable section

variable {d M N Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero N] [NeZero Nc]

omit [NeZero d] in
/-- Equality of terminal owners is symmetric. -/
theorem CMP99SourceActiveRegionChain.sameTerminalBlock_comm
    {N depth : ℕ} {Omega : ActiveGaugeRegion d N}
    (regions : CMP99SourceActiveRegionChain d M N Omega depth)
    (source target : ActiveGaugeRegion.Site Omega) :
    regions.SameTerminalBlock source target ↔
      regions.SameTerminalBlock target source := by
  rw [regions.sameTerminalBlock_iff_terminalSiteOfFine_eq,
    regions.sameTerminalBlock_iff_terminalSiteOfFine_eq]
  exact eq_comm

/-- Within one generated terminal block, every counting-mass kernel block is
an exact scalar multiple of an isometry.  Its norm therefore depends only on
the depth and the norm of the fibre vector, not on either endpoint. -/
theorem CMP99SourceActiveRegionChain.norm_generatedCountingMass_single_apply_of_same
    {N depth : ℕ} {Omega : ActiveGaugeRegion d N}
    (regions : CMP99SourceActiveRegionChain d M N Omega depth)
    (hd : 2 ≤ d) (hM : 2 ≤ M) (rho : SUNAdjointModel Nc) :
    letI : NeZero N := regions.neZero
    ∀ (spacing epsilon : ℝ) (background : GaugeConfig d N (SUN Nc))
      (chain : CMP99SourceUbarRadiusChain d M Nc depth epsilon)
      (fineSmall : ∀ e : ConcreteEdge d N,
        ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
      (source target : ActiveGaugeRegion.Site Omega) (v : SUNLieCoord Nc),
      regions.SameTerminalBlock source target →
      ‖regions.generatedCountingMass hd hM rho spacing epsilon background
          chain fineSmall (singleFinitePiLp source v) target‖ =
        (cmp99SourceBlockAverageWeight M d) ^ (2 * depth) * ‖v‖ := by
  letI : NeZero N := regions.neZero
  induction regions with
  | stop Omega =>
      intro spacing epsilon background chain fineSmall source target v hsame
      have hst : source = target := hsame
      subst target
      change ‖singleFinitePiLp source v source‖ =
        (cmp99SourceBlockAverageWeight M d) ^ (2 * 0) * ‖v‖
      rw [singleFinitePiLp_self]
      simp
  | @step N' depth _ Omega hOmega tail ih =>
      intro spacing epsilon background chain fineSmall source target v hsame
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
      let transport := cmp99SourceWeightedPhysicalTransport rho background
      let Qhead := cmp99SourceTransportedBlockAverageCLM Omega transport
      let sourceCoarse := cmp99ActiveCoarseSiteOfFine Omega hOmega source
      let targetCoarse := cmp99ActiveCoarseSiteOfFine Omega hOmega target
      let sourceValue := cmp99SourceBlockAverageWeight M d •
        transport (blockSite M N' source.1) source.1 v
      let tailMass := tail.generatedCountingMass hd hM rho
        ((M : ℝ) * spacing) (cmp99SourceUbarNextFineRadius d M epsilon)
        Scale.toSourceScale.data.nextBackground chain.tail nextSmall
      have hsameTail : tail.SameTerminalBlock sourceCoarse targetCoarse :=
        hsame
      have haverage : Qhead (singleFinitePiLp source v) =
          singleFinitePiLp sourceCoarse sourceValue := by
        exact cmp99SourceTransportedBlockAverageCLM_single
          Omega hOmega transport source v
      have htail := ih ((M : ℝ) * spacing)
        (cmp99SourceUbarNextFineRadius d M epsilon)
        Scale.toSourceScale.data.nextBackground chain.tail nextSmall
        sourceCoarse targetCoarse sourceValue hsameTail
      have hQadj : Qhead.adjoint =
          cmp99TransportedBlockSynthesisCLM Omega hOmega
            (cmp99SourceBlockAverageWeight M d) transport := by
        dsimp [Qhead]
        exact (cmp99TransportedBlockSynthesisCLM_eq_adjoint Omega hOmega
          (cmp99SourceBlockAverageWeight M d) transport).symm
      change ‖Qhead.adjoint (tailMass
          (Qhead (singleFinitePiLp source v))) target‖ = _
      rw [haverage, hQadj, cmp99TransportedBlockSynthesisCLM_apply]
      change ‖cmp99SourceBlockAverageWeight M d •
          (transport (blockSite M N' target.1) target.1).symm
            (tailMass (singleFinitePiLp sourceCoarse sourceValue)
              targetCoarse)‖ = _
      rw [norm_smul, LinearIsometryEquiv.norm_map, htail]
      have hw : 0 ≤ cmp99SourceBlockAverageWeight M d :=
        cmp99SourceBlockAverageWeight_nonneg M d
      have hsourceValue : ‖sourceValue‖ =
          cmp99SourceBlockAverageWeight M d * ‖v‖ := by
        dsimp [sourceValue]
        rw [norm_smul, LinearIsometryEquiv.norm_map, Real.norm_eq_abs,
          abs_of_nonneg hw]
      rw [Real.norm_eq_abs, abs_of_nonneg hw, hsourceValue]
      calc
        cmp99SourceBlockAverageWeight M d *
            ((cmp99SourceBlockAverageWeight M d) ^ (2 * depth) *
              (cmp99SourceBlockAverageWeight M d * ‖v‖)) =
          ((cmp99SourceBlockAverageWeight M d) ^ (2 * depth) *
            (cmp99SourceBlockAverageWeight M d) ^ 2) * ‖v‖ := by ring
        _ = (cmp99SourceBlockAverageWeight M d) ^ (2 * depth + 2) * ‖v‖ := by
          rw [← pow_add]
        _ = (cmp99SourceBlockAverageWeight M d) ^ (2 * (depth + 1)) * ‖v‖ := by
          rw [show 2 * depth + 2 = 2 * (depth + 1) by omega]

/-- The physical block norms of the generated counting mass are symmetric
under exchanging source and target.  This is stronger than abstract
self-adjointness and is the exact bridge needed between row orientations. -/
theorem CMP99SourceActiveRegionChain.norm_generatedCountingMass_single_apply_comm
    {N depth : ℕ} {Omega : ActiveGaugeRegion d N}
    (regions : CMP99SourceActiveRegionChain d M N Omega depth)
    (hd : 2 ≤ d) (hM : 2 ≤ M) (rho : SUNAdjointModel Nc) :
    letI : NeZero N := regions.neZero
    ∀ (spacing epsilon : ℝ) (background : GaugeConfig d N (SUN Nc))
      (chain : CMP99SourceUbarRadiusChain d M Nc depth epsilon)
      (fineSmall : ∀ e : ConcreteEdge d N,
        ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
      (source target : ActiveGaugeRegion.Site Omega) (v : SUNLieCoord Nc),
      ‖regions.generatedCountingMass hd hM rho spacing epsilon background
          chain fineSmall (singleFinitePiLp source v) target‖ =
        ‖regions.generatedCountingMass hd hM rho spacing epsilon background
          chain fineSmall (singleFinitePiLp target v) source‖ := by
  letI : NeZero N := regions.neZero
  intro spacing epsilon background chain fineSmall source target v
  by_cases hsame : regions.SameTerminalBlock source target
  · rw [regions.norm_generatedCountingMass_single_apply_of_same hd hM rho
        spacing epsilon background chain fineSmall source target v hsame,
      regions.norm_generatedCountingMass_single_apply_of_same hd hM rho
        spacing epsilon background chain fineSmall target source v
        ((regions.sameTerminalBlock_comm source target).1 hsame)]
  · have hsameRev : ¬regions.SameTerminalBlock target source := by
      intro hrev
      exact hsame ((regions.sameTerminalBlock_comm target source).1 hrev)
    rw [regions.generatedCountingMass_single_apply_eq_zero hd hM rho
        spacing epsilon background chain fineSmall source target v hsame,
      regions.generatedCountingMass_single_apply_eq_zero hd hM rho
        spacing epsilon background chain fineSmall target source v hsameRev,
      norm_zero]

/-- The fixed-output unweighted sum has the same exact normalization as the
already verified source-fixed sum, because physical block norms are symmetric.
-/
theorem CMP99SourceActiveRegionChain.sum_norm_generatedCountingMass_single_output
    {N depth : ℕ} {Omega : ActiveGaugeRegion d N}
    (regions : CMP99SourceActiveRegionChain d M N Omega depth)
    (hd : 2 ≤ d) (hM : 2 ≤ M) (rho : SUNAdjointModel Nc) :
    letI : NeZero N := regions.neZero
    ∀ (spacing epsilon : ℝ) (background : GaugeConfig d N (SUN Nc))
      (chain : CMP99SourceUbarRadiusChain d M Nc depth epsilon)
      (fineSmall : ∀ e : ConcreteEdge d N,
        ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
      (target : ActiveGaugeRegion.Site Omega) (v : SUNLieCoord Nc),
      (∑ source,
          ‖regions.generatedCountingMass hd hM rho spacing epsilon background
            chain fineSmall (singleFinitePiLp source v) target‖) =
        (cmp99SourceBlockAverageWeight M d) ^ depth * ‖v‖ := by
  letI : NeZero N := regions.neZero
  intro spacing epsilon background chain fineSmall target v
  calc
    (∑ source,
        ‖regions.generatedCountingMass hd hM rho spacing epsilon background
          chain fineSmall (singleFinitePiLp source v) target‖) =
      ∑ source,
        ‖regions.generatedCountingMass hd hM rho spacing epsilon background
          chain fineSmall (singleFinitePiLp target v) source‖ := by
        apply Finset.sum_congr rfl
        intro source _
        exact regions.norm_generatedCountingMass_single_apply_comm hd hM rho
          spacing epsilon background chain fineSmall source target v
    _ = (cmp99SourceBlockAverageWeight M d) ^ depth * ‖v‖ :=
      regions.sum_norm_generatedCountingMass_single hd hM rho spacing epsilon
        background chain fineSmall target v

/-- The literal generated counting mass satisfies CMP99's fixed-output
weighted orientation with no terminal range-ball cardinality. -/
theorem cmp99SourceIteratedLift_generatedCountingMass_fixedOutputWeighted
    (Omega : ActiveGaugeRegion d N) (depth : ℕ)
    (hd : 2 ≤ d) (hM : 2 ≤ M) (rho : SUNAdjointModel Nc)
    (spacing epsilon rate : ℝ) (hrate : 0 ≤ rate)
    (background : GaugeConfig d (cmp99RegionalLatticeSize M N depth) (SUN Nc))
    (chain : CMP99SourceUbarRadiusChain d M Nc depth epsilon)
    (fineSmall : ∀ e : ConcreteEdge d (cmp99RegionalLatticeSize M N depth),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon) :
    let regions := cmp99SourceIteratedLiftActiveRegionChain
      (M := M) Omega depth
    FinitePiLpTypedFixedOutputWeightedKernelBound
      (ι := ActiveGaugeRegion.Site
        (cmp99IteratedLiftActiveRegion (M := M) Omega depth))
      (κ := ActiveGaugeRegion.Site
        (cmp99IteratedLiftActiveRegion (M := M) Omega depth))
      (g := SUNLieCoord Nc)
      (regions.generatedCountingMass hd hM rho spacing epsilon background
        chain fineSmall)
      (fun target source => finBoxDist target.1 source.1)
      (Real.exp (rate * ((M ^ depth - 1 : ℕ) : ℝ)) *
        (cmp99SourceBlockAverageWeight M d) ^ depth) rate := by
  dsimp only
  let regions := cmp99SourceIteratedLiftActiveRegionChain
    (M := M) Omega depth
  apply finitePiLpTypedFixedOutputWeightedKernelBound_of_outputSum_and_finiteRange
  · exact pow_nonneg (cmp99SourceBlockAverageWeight_nonneg M d) depth
  · exact hrate
  · exact cmp99SourceIteratedLift_generatedCountingMass_finiteRange
      Omega depth hd hM rho spacing epsilon background chain fineSmall
  · intro target v
    exact (regions.sum_norm_generatedCountingMass_single_output hd hM rho
      spacing epsilon background chain fineSmall target v).le

/-- Literal `Q'^*Q'` spelling of the same fixed-output estimate. -/
theorem cmp99SourceIteratedLift_QprimeMass_fixedOutputWeighted
    (Omega : ActiveGaugeRegion d N) (depth : ℕ)
    (hd : 2 ≤ d) (hM : 2 ≤ M) (rho : SUNAdjointModel Nc)
    (spacing epsilon rate : ℝ) (hrate : 0 ≤ rate)
    (background : GaugeConfig d (cmp99RegionalLatticeSize M N depth) (SUN Nc))
    (chain : CMP99SourceUbarRadiusChain d M Nc depth epsilon)
    (fineSmall : ∀ e : ConcreteEdge d (cmp99RegionalLatticeSize M N depth),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon) :
    let regions := cmp99SourceIteratedLiftActiveRegionChain
      (M := M) Omega depth
    let T := regions.weightedQprimeTower hd hM rho spacing epsilon background
      chain fineSmall
    FinitePiLpTypedFixedOutputWeightedKernelBound
      (ι := ActiveGaugeRegion.Site
        (cmp99IteratedLiftActiveRegion (M := M) Omega depth))
      (κ := ActiveGaugeRegion.Site
        (cmp99IteratedLiftActiveRegion (M := M) Omega depth))
      (g := SUNLieCoord Nc)
      (T.Qprime.adjoint.comp T.Qprime)
      (fun target source => finBoxDist target.1 source.1)
      (Real.exp (rate * ((M ^ depth - 1 : ℕ) : ℝ)) *
        (cmp99SourceBlockAverageWeight M d) ^ depth) rate := by
  dsimp only
  let regions := cmp99SourceIteratedLiftActiveRegionChain
    (M := M) Omega depth
  let T := regions.weightedQprimeTower hd hM rho spacing epsilon background
    chain fineSmall
  change FinitePiLpTypedFixedOutputWeightedKernelBound
    (T.Qprime.adjoint.comp T.Qprime)
    (fun target source => finBoxDist target.1 source.1)
    (Real.exp (rate * ((M ^ depth - 1 : ℕ) : ℝ)) *
      (cmp99SourceBlockAverageWeight M d) ^ depth) rate
  rw [← regions.generatedCountingMass_eq_QprimeMass hd hM rho spacing epsilon
    background chain fineSmall]
  exact cmp99SourceIteratedLift_generatedCountingMass_fixedOutputWeighted
    Omega depth hd hM rho spacing epsilon rate hrate background chain fineSmall

end

end YangMills.RG
