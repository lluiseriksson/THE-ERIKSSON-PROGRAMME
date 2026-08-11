/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceFlatGeneratedQprimeAdjointDictionary
import YangMills.RG.BalabanCMP99SourceGeneratedWeightedAdjointRange

/-!
PRE-VALIDATION: source is present, its `.olean` has not yet been materialized,
and the result has not yet been verified by the Lean compiler.

# Exact terminal-owner action of the flat generated `Q'`

The typed flat recursion is not silently identified with a separately
reconstructed one-block operator.  Instead this file first proves its exact
action on coordinate probes.  A fine probe reaches its recursively generated
terminal owner with coefficient `(M^{-d})^depth`; the reverse coefficient-one
synthesis reads precisely that owner.  Consequently both the printed
source-weighted mass and Lean's counting-adjoint mass have explicit kernels.

This is the source-faithful precursor to a one-block collapse.  It does not
identify the terminal coordinate type with a full coarse box, identify CMP99
strata, match a precision, construct an inverse or prove a Green bound.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator RealInnerProductSpace

noncomputable section

variable {d M N Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero N] [NeZero Nc]

/-- A coordinate probe is averaged to its exact recursively generated terminal
owner, with one literal factor `M^{-d}` per scale. -/
theorem CMP99SourceActiveRegionChain.flatExplicitQprime_single
    {N depth : ℕ} {Omega : ActiveGaugeRegion d N}
    (regions : CMP99SourceActiveRegionChain d M N Omega depth) :
    letI : NeZero N := regions.neZero
    ∀ (source : ActiveGaugeRegion.Site Omega) (v : SUNLieCoord Nc),
      regions.flatExplicitQprime (Nc := Nc) (singleFinitePiLp source v) =
        singleFinitePiLp (regions.terminalSiteOfFine source)
          ((cmp99SourceBlockAverageWeight M d) ^ depth • v) := by
  letI : NeZero N := regions.neZero
  induction regions with
  | stop Omega =>
      intro source v
      change (ContinuousLinearMap.id ℝ _)
          (singleFinitePiLp source v) =
        singleFinitePiLp source
          ((cmp99SourceBlockAverageWeight M d) ^ 0 • v)
      simp
  | @step N' depth _ Omega hOmega tail ih =>
      letI : NeZero (M * N') := inferInstance
      intro source v
      let sourceCoarse := cmp99ActiveCoarseSiteOfFine Omega hOmega source
      have haverage :
          cmp99SourceFlatRealBlockAverageCLM Omega
              (singleFinitePiLp source v) =
            singleFinitePiLp sourceCoarse
              (cmp99SourceBlockAverageWeight M d • v) := by
        simpa [cmp99SourceFlatRealBlockAverageCLM, sourceCoarse] using
          (cmp99SourceTransportedBlockAverageCLM_single
            Omega hOmega
              (cmp99SourceFlatRealTransport
                (d := d) (M := M) (N' := N') (Nc := Nc)) source v)
      change tail.flatExplicitQprime (Nc := Nc)
          (cmp99SourceFlatRealBlockAverageCLM Omega
            (singleFinitePiLp source v)) = _
      rw [haverage, ih]
      change singleFinitePiLp (tail.terminalSiteOfFine sourceCoarse)
          ((cmp99SourceBlockAverageWeight M d) ^ depth •
            (cmp99SourceBlockAverageWeight M d • v)) =
        singleFinitePiLp (tail.terminalSiteOfFine sourceCoarse)
          ((cmp99SourceBlockAverageWeight M d) ^ (depth + 1) • v)
      congr 1
      rw [pow_succ, smul_smul]

/-- The reverse coefficient-one recursion reads the terminal coordinate owned
by each fine site, with no additional normalization. -/
theorem CMP99SourceActiveRegionChain.flatExplicitWeightedAdjoint_apply
    {N depth : ℕ} {Omega : ActiveGaugeRegion d N}
    (regions : CMP99SourceActiveRegionChain d M N Omega depth) :
    letI : NeZero N := regions.neZero
    ∀ (eta : PiLp 2 (fun _ : regions.terminalSite => SUNLieCoord Nc))
      (source : ActiveGaugeRegion.Site Omega),
      regions.flatExplicitWeightedAdjoint (Nc := Nc) eta source =
        eta (regions.terminalSiteOfFine source) := by
  letI : NeZero N := regions.neZero
  induction regions with
  | stop Omega =>
      intro eta source
      rfl
  | @step N' depth _ Omega hOmega tail ih =>
      letI : NeZero (M * N') := inferInstance
      intro eta source
      change cmp99SourceFlatRealBlockWeightedAdjointCLM Omega hOmega
          (tail.flatExplicitWeightedAdjoint (Nc := Nc) eta) source = _
      rw [← cmp99SourceTransportedBlockWeightedAdjointCLM_flat_eq_explicit
        Omega hOmega (matrixSUNAdjointModel Nc)]
      rw [cmp99SourceTransportedBlockWeightedAdjointCLM_flat_apply]
      exact ih _ _

/-- Exact kernel of the source-weighted generated mass.  It has coefficient
`(M^{-d})^depth` precisely inside one terminal-owner fibre and vanishes
outside it. -/
theorem CMP99SourceActiveRegionChain.flatExplicitWeightedMass_single_apply
    {N depth : ℕ} {Omega : ActiveGaugeRegion d N}
    (regions : CMP99SourceActiveRegionChain d M N Omega depth) :
    letI : NeZero N := regions.neZero
    ∀ (source target : ActiveGaugeRegion.Site Omega) (v : SUNLieCoord Nc),
      ((regions.flatExplicitWeightedAdjoint (Nc := Nc)).comp
          (regions.flatExplicitQprime (Nc := Nc)))
            (singleFinitePiLp source v) target =
        if regions.terminalSiteOfFine target =
            regions.terminalSiteOfFine source then
          (cmp99SourceBlockAverageWeight M d) ^ depth • v
        else 0 := by
  letI : NeZero N := regions.neZero
  intro source target v
  rw [ContinuousLinearMap.comp_apply, regions.flatExplicitQprime_single,
    regions.flatExplicitWeightedAdjoint_apply]
  by_cases howner : regions.terminalSiteOfFine target =
      regions.terminalSiteOfFine source
  · rw [if_pos howner, howner, singleFinitePiLp_self]
  · rw [if_neg howner]
    exact singleFinitePiLp_of_ne _ howner

/-- Exact kernel of Lean's counting-adjoint generated mass.  The additional
adjoint normalization contributes the second factor `(M^{-d})^depth`. -/
theorem CMP99SourceActiveRegionChain.flatExplicitCountingMass_single_apply
    {N depth : ℕ} {Omega : ActiveGaugeRegion d N}
    (regions : CMP99SourceActiveRegionChain d M N Omega depth) :
    letI : NeZero N := regions.neZero
    ∀ (source target : ActiveGaugeRegion.Site Omega) (v : SUNLieCoord Nc),
      ((regions.flatExplicitQprime (Nc := Nc)).adjoint.comp
          (regions.flatExplicitQprime (Nc := Nc)))
            (singleFinitePiLp source v) target =
        if regions.terminalSiteOfFine target =
            regions.terminalSiteOfFine source then
          (cmp99SourceBlockAverageWeight M d) ^ (2 * depth) • v
        else 0 := by
  letI : NeZero N := regions.neZero
  intro source target v
  rw [regions.flatExplicitQprime_adjoint_comp_eq]
  change (cmp99SourceBlockAverageWeight M d) ^ depth •
      (((regions.flatExplicitWeightedAdjoint (Nc := Nc)).comp
        (regions.flatExplicitQprime (Nc := Nc)))
          (singleFinitePiLp source v)) target = _
  rw [regions.flatExplicitWeightedMass_single_apply]
  by_cases howner : regions.terminalSiteOfFine target =
      regions.terminalSiteOfFine source
  · rw [if_pos howner, if_pos howner, smul_smul]
    congr 1
    rw [show 2 * depth = depth + depth by omega, pow_add]
  · rw [if_neg howner, if_neg howner, smul_zero]

end

end YangMills.RG
