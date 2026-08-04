/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceGeneratedQprimeRowMass
import YangMills.RG.BalabanCMP99SourceTransportedBlockSynthesisRowSum
import YangMills.RG.FinitePiLpTypedWeightedRowFromRange

/-!
# Exact source rows of the generated CMP99 counting mass

PRE-VALIDATION: this source is present, but its `.olean` has not yet been
materialized and its result is not compiler-verified.

The load-bearing mass in the source precision is `Q'^* Q'`, not `Q'` alone.
At one scale `Q'` sends a source delta to one owner with coefficient `M^{-d}`;
the counting adjoint then spreads the result over the complete block with
exact total row cost one.  Iterating the literal `generatedCountingMass`
therefore leaves the exact amplitude `(M^{-d})^depth`.  No range-ball
cardinality is introduced.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator RealInnerProductSpace BigOperators

noncomputable section

variable {d M N Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero N] [NeZero Nc]

/-- The recursively generated counting mass `Q'^*Q'` has exact source-row
mass `(M^{-d})^depth`. -/
theorem CMP99SourceActiveRegionChain.sum_norm_generatedCountingMass_single
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
          ‖regions.generatedCountingMass hd hM rho spacing epsilon background
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
      let Qhead := cmp99SourceTransportedBlockAverageCLM Omega transport
      let sourceCoarse := cmp99ActiveCoarseSiteOfFine Omega hOmega source
      let sourceValue := cmp99SourceBlockAverageWeight M d •
        transport (blockSite M N' source.1) source.1 v
      let tailMass := tail.generatedCountingMass hd hM rho
        ((M : ℝ) * spacing) (cmp99SourceUbarNextFineRadius d M epsilon)
        Scale.toSourceScale.data.nextBackground chain.tail nextSmall
      have haverage : Qhead (singleFinitePiLp source v) =
          singleFinitePiLp sourceCoarse sourceValue := by
        exact cmp99SourceTransportedBlockAverageCLM_single
          Omega hOmega transport source v
      have htail := ih ((M : ℝ) * spacing)
        (cmp99SourceUbarNextFineRadius d M epsilon)
        Scale.toSourceScale.data.nextBackground chain.tail nextSmall
        sourceCoarse sourceValue
      change (∑ target,
          ‖Qhead.adjoint (tailMass (Qhead
            (singleFinitePiLp source v))) target‖) = _
      rw [haverage]
      calc
        (∑ target,
            ‖Qhead.adjoint
              (tailMass (singleFinitePiLp sourceCoarse sourceValue))
                target‖) =
            ∑ y, ‖tailMass
              (singleFinitePiLp sourceCoarse sourceValue) y‖ := by
          simpa [Qhead, transport] using
            sum_norm_cmp99SourceTransportedBlockAverage_adjoint
              Omega hOmega transport
              (tailMass (singleFinitePiLp sourceCoarse sourceValue))
        _ = (cmp99SourceBlockAverageWeight M d) ^ depth *
            ‖sourceValue‖ := htail
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
              rw [pow_succ]

/-- Inequality form of the exact generated counting-mass row. -/
theorem CMP99SourceActiveRegionChain.sum_norm_generatedCountingMass_single_le
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
          ‖regions.generatedCountingMass hd hM rho spacing epsilon background
              chain fineSmall (singleFinitePiLp source v) target‖) ≤
        (cmp99SourceBlockAverageWeight M d) ^ depth * ‖v‖ := by
  letI : NeZero N := regions.neZero
  intro spacing epsilon background chain fineSmall source v
  exact (regions.sum_norm_generatedCountingMass_single hd hM rho spacing
    epsilon background chain fineSmall source v).le

/-- The canonical generated counting mass has a fixed-rate weighted row with
only the maximal range weight as cost. -/
theorem cmp99SourceIteratedLift_generatedCountingMass_weightedRow
    (Omega : ActiveGaugeRegion d N) (depth : ℕ)
    (hd : 2 ≤ d) (hM : 2 ≤ M) (rho : SUNAdjointModel Nc)
    (spacing epsilon rate : ℝ) (hrate : 0 ≤ rate)
    (background : GaugeConfig d (cmp99RegionalLatticeSize M N depth) (SUN Nc))
    (chain : CMP99SourceUbarRadiusChain d M Nc depth epsilon)
    (fineSmall : ∀ e : ConcreteEdge d (cmp99RegionalLatticeSize M N depth),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon) :
    let regions := cmp99SourceIteratedLiftActiveRegionChain
      (M := M) Omega depth
    FinitePiLpTypedWeightedRowKernelBound
      (regions.generatedCountingMass hd hM rho spacing epsilon background
        chain fineSmall)
      (fun target source => finBoxDist target.1 source.1)
      (Real.exp (rate * ((M ^ depth - 1 : ℕ) : ℝ)) *
        (cmp99SourceBlockAverageWeight M d) ^ depth) rate := by
  dsimp only
  let regions := cmp99SourceIteratedLiftActiveRegionChain
    (M := M) Omega depth
  apply finitePiLpTypedWeightedRowKernelBound_of_rowSum_and_finiteRange
  · exact pow_nonneg (cmp99SourceBlockAverageWeight_nonneg M d) depth
  · exact hrate
  · exact cmp99SourceIteratedLift_generatedCountingMass_finiteRange
      Omega depth hd hM rho spacing epsilon background chain fineSmall
  · exact regions.sum_norm_generatedCountingMass_single_le hd hM rho spacing
      epsilon background chain fineSmall

/-- Literal `Q'^*Q'` form of the same weighted-row estimate. -/
theorem cmp99SourceIteratedLift_QprimeMass_weightedRow
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
    FinitePiLpTypedWeightedRowKernelBound
      (T.Qprime.adjoint.comp T.Qprime)
      (fun target source => finBoxDist target.1 source.1)
      (Real.exp (rate * ((M ^ depth - 1 : ℕ) : ℝ)) *
        (cmp99SourceBlockAverageWeight M d) ^ depth) rate := by
  dsimp only
  let regions := cmp99SourceIteratedLiftActiveRegionChain
    (M := M) Omega depth
  let T := regions.weightedQprimeTower hd hM rho spacing epsilon background
    chain fineSmall
  change FinitePiLpTypedWeightedRowKernelBound
    (T.Qprime.adjoint.comp T.Qprime)
    (fun target source => finBoxDist target.1 source.1)
    (Real.exp (rate * ((M ^ depth - 1 : ℕ) : ℝ)) *
      (cmp99SourceBlockAverageWeight M d) ^ depth) rate
  rw [← regions.generatedCountingMass_eq_QprimeMass hd hM rho spacing epsilon
    background chain fineSmall]
  exact cmp99SourceIteratedLift_generatedCountingMass_weightedRow
    Omega depth hd hM rho spacing epsilon rate hrate background chain fineSmall

end

end YangMills.RG
