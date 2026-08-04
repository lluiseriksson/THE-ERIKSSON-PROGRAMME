/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceGeneratedMassRange
import YangMills.RG.BalabanCMP99SourceGeneratedTerminalCoordinates
import YangMills.RG.BalabanCMP99SourceGeneratedWeightedAdjointRange

/-!
# Exact source-row mass of the generated CMP99 average

PRE-VALIDATION: this source is present, but its `.olean` has not yet been
materialized and its result is not compiler-verified.

Every literal one-step average sends a source delta to the delta at its owner
block, with coefficient `M^{-d}`.  Iterating the generated physical tower
therefore gives the exact row amplitude `(M^{-d})^depth`; no range-ball or
ambient-volume cardinality enters.  This is the normalization input needed
before finite range adds only the factor `exp (rate * range)`.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator RealInnerProductSpace BigOperators

noncomputable section

variable {d M N Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero N] [NeZero Nc]

/-- The `l1` target sum of a single coordinate field is its coefficient
norm. -/
theorem sum_norm_singleFinitePiLp
    {ι g : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup g] [NormedSpace ℝ g]
    (source : ι) (v : g) :
    (∑ target : ι, ‖singleFinitePiLp source v target‖) = ‖v‖ := by
  classical
  rw [Fintype.sum_eq_single source]
  · rw [singleFinitePiLp_self]
  · intro target hne
    rw [singleFinitePiLp_of_ne v hne]
    exact norm_zero

/-- One literal source average has exact row mass `M^{-d}`.  The transported
coefficient has the same norm because the background transport is an
isometry. -/
theorem sum_norm_cmp99SourceTransportedBlockAverageCLM_single
    {N' : ℕ} [NeZero N']
    (Omega : ActiveGaugeRegion d (M * N')) (hOmega : Omega.BlockSaturated)
    (transport : FinBox d N' → FinBox d (M * N') →
      (SUNLieCoord Nc ≃ₗᵢ[ℝ] SUNLieCoord Nc))
    (source : ActiveGaugeRegion.Site Omega) (v : SUNLieCoord Nc) :
    (∑ target,
        ‖cmp99SourceTransportedBlockAverageCLM Omega transport
            (singleFinitePiLp source v) target‖) =
      cmp99SourceBlockAverageWeight M d * ‖v‖ := by
  rw [cmp99SourceTransportedBlockAverageCLM_single
    Omega hOmega transport source v, sum_norm_singleFinitePiLp,
    norm_smul, LinearIsometryEquiv.norm_map, Real.norm_eq_abs,
    abs_of_nonneg (cmp99SourceBlockAverageWeight_nonneg M d)]

/-- The recursively generated `Q'_depth` with its terminal coordinate type
exposed.  This is built from the literal one-step physical averages; no
terminal operator is supplied by the caller. -/
noncomputable def CMP99SourceActiveRegionChain.physicalQprime
    {N depth : ℕ} {Omega : ActiveGaugeRegion d N}
    (regions : CMP99SourceActiveRegionChain d M N Omega depth)
    (hd : 2 ≤ d) (hM : 2 ≤ M) (rho : SUNAdjointModel Nc) :
    letI : NeZero N := regions.neZero
    (spacing epsilon : ℝ) → (background : GaugeConfig d N (SUN Nc)) →
    (chain : CMP99SourceUbarRadiusChain d M Nc depth epsilon) →
    (fineSmall : ∀ e : ConcreteEdge d N,
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon) →
    ActiveGaugeZeroCochain Omega (SUNLieCoord Nc) →L[ℝ]
      PiLp 2 (fun _ : regions.terminalSite => SUNLieCoord Nc) := by
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
      exact (ih ((M : ℝ) * spacing)
        (cmp99SourceUbarNextFineRadius d M epsilon)
        Scale.toSourceScale.data.nextBackground chain.tail nextSmall).comp
          (cmp99SourceTransportedBlockAverageCLM Omega
            (cmp99SourceWeightedPhysicalTransport rho background))

/-- The original bundled generated `Q'_depth`, transported only to expose
the canonical terminal coordinate type. -/
noncomputable def CMP99SourceActiveRegionChain.transportedQprime
    {N depth : ℕ} {Omega : ActiveGaugeRegion d N}
    (regions : CMP99SourceActiveRegionChain d M N Omega depth)
    (hd : 2 ≤ d) (hM : 2 ≤ M) (rho : SUNAdjointModel Nc) :
    letI : NeZero N := regions.neZero
    (spacing epsilon : ℝ) → (background : GaugeConfig d N (SUN Nc)) →
    (chain : CMP99SourceUbarRadiusChain d M Nc depth epsilon) →
    (fineSmall : ∀ e : ConcreteEdge d N,
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon) →
    ActiveGaugeZeroCochain Omega (SUNLieCoord Nc) →L[ℝ]
      PiLp 2 (fun _ : regions.terminalSite => SUNLieCoord Nc) := by
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
    (E := cmp99SourcePhysicalTerminalHilbertSpace Nc Omega)
    (F := T.TerminalSpace)
    (E' := cmp99SourcePhysicalTerminalHilbertSpace Nc Omega)
    (F' := regions.terminalCoordinateHilbertSpace (Nc := Nc))
    rfl (hT.trans hCoord) T.Qprime

/-- The direct recursive coordinate realization is exactly the bundled
generated tower after canonical terminal transport. -/
theorem CMP99SourceActiveRegionChain.physicalQprime_eq_transported
    {N depth : ℕ} {Omega : ActiveGaugeRegion d N}
    (regions : CMP99SourceActiveRegionChain d M N Omega depth)
    (hd : 2 ≤ d) (hM : 2 ≤ M) (rho : SUNAdjointModel Nc) :
    letI : NeZero N := regions.neZero
    ∀ (spacing epsilon : ℝ) (background : GaugeConfig d N (SUN Nc))
      (chain : CMP99SourceUbarRadiusChain d M Nc depth epsilon)
      (fineSmall : ∀ e : ConcreteEdge d N,
        ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon),
      regions.physicalQprime hd hM rho spacing epsilon background
          chain fineSmall =
        regions.transportedQprime hd hM rho spacing epsilon background
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
      change (tail.physicalQprime hd hM rho ((M : ℝ) * spacing)
          (cmp99SourceUbarNextFineRadius d M epsilon)
          Scale.toSourceScale.data.nextBackground chain.tail nextSmall).comp
            (cmp99SourceTransportedBlockAverageCLM Omega
              (cmp99SourceWeightedPhysicalTransport rho background)) = _
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
      let Head := cmp99SourceTransportedBlockAverageCLM Omega
        (cmp99SourceWeightedPhysicalTransport rho background)
      have hcomp := cmp99SourceTerminalCLMTransport_comp
        (E := cmp99SourcePhysicalTerminalHilbertSpace Nc Omega)
        (F := cmp99SourcePhysicalTerminalHilbertSpace Nc
          (cmp99ActiveCoarseRegion (M := M) (N' := N') Omega))
        (G := tailT.TerminalSpace)
        (E' := cmp99SourcePhysicalTerminalHilbertSpace Nc Omega)
        (F' := cmp99SourcePhysicalTerminalHilbertSpace Nc
          (cmp99ActiveCoarseRegion (M := M) (N' := N') Omega))
        (G' := tail.terminalCoordinateHilbertSpace (Nc := Nc))
        rfl rfl (hTailT.trans hTailCoord) tailT.Qprime Head
      simpa [transportedQprime, tailT, Head] using hcomp

/-- A generated physical `Q'_depth` has literal source-row mass exactly
`(M^{-d})^depth`.  The background transports are isometries and hence do not
alter the coefficient. -/
theorem CMP99SourceActiveRegionChain.sum_norm_physicalQprime_single
    {depth : ℕ} {Omega : ActiveGaugeRegion d N}
    (regions : CMP99SourceActiveRegionChain d M N Omega depth)
    (hd : 2 ≤ d) (hM : 2 ≤ M) (rho : SUNAdjointModel Nc) :
    letI : NeZero N := regions.neZero
    ∀ (spacing epsilon : ℝ) (background : GaugeConfig d N (SUN Nc))
      (chain : CMP99SourceUbarRadiusChain d M Nc depth epsilon)
      (fineSmall : ∀ e : ConcreteEdge d N,
        ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
      (source : ActiveGaugeRegion.Site Omega) (v : SUNLieCoord Nc),
      (∑ target,
          ‖regions.physicalQprime hd hM rho spacing epsilon background
              chain fineSmall (singleFinitePiLp source v) target‖) =
        (cmp99SourceBlockAverageWeight M d) ^ depth * ‖v‖ := by
  letI : NeZero N := regions.neZero
  induction regions with
  | stop Omega =>
      intro spacing epsilon background chain fineSmall source v
      change (∑ target, ‖singleFinitePiLp source v target‖) =
        (cmp99SourceBlockAverageWeight M d) ^ 0 * ‖v‖
      rw [sum_norm_singleFinitePiLp]
      simp
  | @step N' depth _ Omega hOmega tail ih =>
      intro spacing epsilon background chain fineSmall source v
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
      let sourceCoarse := cmp99ActiveCoarseSiteOfFine Omega hOmega source
      let sourceValue := cmp99SourceBlockAverageWeight M d •
        transport (blockSite M N' source.1) source.1 v
      let tailQprime := tail.physicalQprime hd hM rho
        ((M : ℝ) * spacing) (cmp99SourceUbarNextFineRadius d M epsilon)
        Scale.toSourceScale.data.nextBackground chain.tail nextSmall
      have haverage :
          cmp99SourceTransportedBlockAverageCLM Omega transport
              (singleFinitePiLp source v) =
            singleFinitePiLp sourceCoarse sourceValue := by
        exact cmp99SourceTransportedBlockAverageCLM_single
          Omega hOmega transport source v
      have htail := ih ((M : ℝ) * spacing)
        (cmp99SourceUbarNextFineRadius d M epsilon)
        Scale.toSourceScale.data.nextBackground chain.tail nextSmall
        sourceCoarse sourceValue
      change (∑ target,
          ‖tailQprime
            (cmp99SourceTransportedBlockAverageCLM Omega transport
              (singleFinitePiLp source v)) target‖) = _
      rw [haverage]
      calc
        (∑ target, ‖tailQprime
            (singleFinitePiLp sourceCoarse sourceValue) target‖) =
            (cmp99SourceBlockAverageWeight M d) ^ depth * ‖sourceValue‖ :=
          htail
        _ = (cmp99SourceBlockAverageWeight M d) ^ (depth + 1) * ‖v‖ := by
          have hsourceValueNorm : ‖sourceValue‖ =
              cmp99SourceBlockAverageWeight M d * ‖v‖ := by
            dsimp [sourceValue]
            rw [norm_smul, LinearIsometryEquiv.norm_map, Real.norm_eq_abs,
              abs_of_nonneg (cmp99SourceBlockAverageWeight_nonneg M d)]
          rw [hsourceValueNorm]
          calc
            (cmp99SourceBlockAverageWeight M d) ^ depth *
                (cmp99SourceBlockAverageWeight M d * ‖v‖) =
              ((cmp99SourceBlockAverageWeight M d) ^ depth *
                cmp99SourceBlockAverageWeight M d) * ‖v‖ := by ring
            _ = (cmp99SourceBlockAverageWeight M d) ^ (depth + 1) * ‖v‖ := by
              congr 1

/-- Inequality form of the exact generated source-row mass, for direct use by
weighted-row adapters. -/
theorem CMP99SourceActiveRegionChain.sum_norm_physicalQprime_single_le
    {depth : ℕ} {Omega : ActiveGaugeRegion d N}
    (regions : CMP99SourceActiveRegionChain d M N Omega depth)
    (hd : 2 ≤ d) (hM : 2 ≤ M) (rho : SUNAdjointModel Nc) :
    letI : NeZero N := regions.neZero
    ∀ (spacing epsilon : ℝ) (background : GaugeConfig d N (SUN Nc))
      (chain : CMP99SourceUbarRadiusChain d M Nc depth epsilon)
      (fineSmall : ∀ e : ConcreteEdge d N,
        ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
      (source : ActiveGaugeRegion.Site Omega) (v : SUNLieCoord Nc),
      (∑ target,
          ‖regions.physicalQprime hd hM rho spacing epsilon background
              chain fineSmall (singleFinitePiLp source v) target‖) ≤
        (cmp99SourceBlockAverageWeight M d) ^ depth * ‖v‖ := by
  letI : NeZero N := regions.neZero
  intro spacing epsilon background chain fineSmall source v
  exact (regions.sum_norm_physicalQprime_single hd hM rho spacing epsilon
    background chain fineSmall source v).le

end

end YangMills.RG
