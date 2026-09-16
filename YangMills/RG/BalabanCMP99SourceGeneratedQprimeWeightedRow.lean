/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceGeneratedQprimeRowMass
import YangMills.RG.BalabanCMP99SourceGeneratedWeightedAdjointRange
import YangMills.RG.FinitePiLpTypedWeightedRowFromRange

/-!
# Weighted source rows of the generated CMP99 average

The literal generated `Q'_depth` sends a fine source delta only to its
terminal owner.  Combining this exact support with the source-row mass
`(M^{-d})^depth` gives a weighted row bound with the sole range cost
`exp (rate * (M^depth - 1))`; no range-ball cardinality is introduced.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator RealInnerProductSpace BigOperators

noncomputable section

variable {d M N Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero N] [NeZero Nc]

/-- A fine coordinate probe is sent only to its recursively generated
terminal owner. -/
theorem CMP99SourceActiveRegionChain.physicalQprime_single_apply_eq_zero
    {N depth : ℕ} {Omega : ActiveGaugeRegion d N}
    (regions : CMP99SourceActiveRegionChain d M N Omega depth)
    (hd : 2 ≤ d) (hM : 2 ≤ M) (rho : SUNAdjointModel Nc) :
    letI : NeZero N := regions.neZero
    ∀ (spacing epsilon : ℝ) (background : GaugeConfig d N (SUN Nc))
      (chain : CMP99SourceUbarRadiusChain d M Nc depth epsilon)
      (fineSmall : ∀ e : ConcreteEdge d N,
        ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
      (source : ActiveGaugeRegion.Site Omega)
      (target : regions.terminalSite) (v : SUNLieCoord Nc),
      target ≠ regions.terminalSiteOfFine source →
      regions.physicalQprime hd hM rho spacing epsilon background
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
      let sourceCoarse := cmp99ActiveCoarseSiteOfFine Omega hOmega source
      let sourceValue := cmp99SourceBlockAverageWeight M d •
        cmp99SourceWeightedPhysicalTransport rho background
          (blockSite M N' source.1) source.1 v
      have haverage :
          cmp99SourceTransportedBlockAverageCLM Omega
              (cmp99SourceWeightedPhysicalTransport rho background)
              (singleFinitePiLp source v) =
            singleFinitePiLp sourceCoarse sourceValue := by
        exact cmp99SourceTransportedBlockAverageCLM_single Omega hOmega
          (cmp99SourceWeightedPhysicalTransport rho background) source v
      change tail.physicalQprime hd hM rho ((M : ℝ) * spacing)
          (cmp99SourceUbarNextFineRadius d M epsilon)
          Scale.toSourceScale.data.nextBackground chain.tail nextSmall
          (cmp99SourceTransportedBlockAverageCLM Omega
            (cmp99SourceWeightedPhysicalTransport rho background)
            (singleFinitePiLp source v)) target = 0
      rw [haverage]
      exact ih ((M : ℝ) * spacing)
        (cmp99SourceUbarNextFineRadius d M epsilon)
        Scale.toSourceScale.data.nextBackground chain.tail nextSmall
        sourceCoarse target sourceValue hne

/-- The canonical generated `Q'_depth` has rectangular range
`M^depth - 1`, measured from each terminal target representative to the fine
source coordinate. -/
theorem cmp99SourceIteratedLift_physicalQprime_finiteRange
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
      (ι := ActiveGaugeRegion.Site
        (cmp99IteratedLiftActiveRegion (M := M) Omega depth))
      (κ := regions.terminalSite) (g := SUNLieCoord Nc)
      (regions.physicalQprime hd hM rho spacing epsilon background
        chain fineSmall)
      (fun target source => finBoxDist source.1
        (regions.terminalRepresentative target).1)
      (M ^ depth - 1) := by
  dsimp only
  let regions := cmp99SourceIteratedLiftActiveRegionChain
    (M := M) Omega depth
  intro source target v hfar
  apply regions.physicalQprime_single_apply_eq_zero
    hd hM rho spacing epsilon background chain fineSmall source target v
  exact (regions.terminalSiteOfFine_ne_of_dist_gt
    (fun x y => finBoxDist x.1 y.1) (M ^ depth - 1)
    (cmp99SourceIteratedLift_terminalBlock_diameter
      (M := M) Omega depth) target source hfar).symm

/-- Exact source-row normalization plus terminal-block range yield the
fixed-rate weighted row estimate for the literal generated `Q'_depth`.
Only the maximal exponential weight is paid. -/
theorem cmp99SourceIteratedLift_physicalQprime_weightedRow
    (Omega : ActiveGaugeRegion d N) (depth : ℕ)
    (hd : 2 ≤ d) (hM : 2 ≤ M) (rho : SUNAdjointModel Nc)
    (spacing epsilon rate : ℝ) (hrate : 0 ≤ rate)
    (background : GaugeConfig d (cmp99RegionalLatticeSize M N depth) (SUN Nc))
    (chain : CMP99SourceUbarRadiusChain d M Nc depth epsilon)
    (fineSmall : ∀ e : ConcreteEdge d
      (cmp99RegionalLatticeSize M N depth),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon) :
    let regions := cmp99SourceIteratedLiftActiveRegionChain
      (M := M) Omega depth
    FinitePiLpTypedWeightedRowKernelBound
      (ι := ActiveGaugeRegion.Site
        (cmp99IteratedLiftActiveRegion (M := M) Omega depth))
      (κ := regions.terminalSite) (g := SUNLieCoord Nc)
      (regions.physicalQprime hd hM rho spacing epsilon background
        chain fineSmall)
      (fun target source => finBoxDist source.1
        (regions.terminalRepresentative target).1)
      (Real.exp (rate * ((M ^ depth - 1 : ℕ) : ℝ)) *
        (cmp99SourceBlockAverageWeight M d) ^ depth) rate := by
  dsimp only
  let regions := cmp99SourceIteratedLiftActiveRegionChain
    (M := M) Omega depth
  apply finitePiLpTypedWeightedRowKernelBound_of_rowSum_and_finiteRange
  · exact pow_nonneg (cmp99SourceBlockAverageWeight_nonneg M d) depth
  · exact hrate
  · exact cmp99SourceIteratedLift_physicalQprime_finiteRange
      Omega depth hd hM rho spacing epsilon background chain fineSmall
  · exact regions.sum_norm_physicalQprime_single_le hd hM rho spacing epsilon
      background chain fineSmall

end

end YangMills.RG
