import YangMills.RG.BalabanCMP99SourceFlatGeneratedQprimeTerminalOwner

/-!
PRE-VALIDATION: source present, .olean not materialized, not compiler-verified.

R2d.2a exact field action of the already constructed flat generated Q'.
The point-source producer is consumed internally; no arbitrary kernel or
operator equality is supplied. The complete finite field is decomposed
using sum_singleFinitePiLp_eq, with one unchanged averaging weight per scale.

This works over the actual active-site type and makes NO full-fibre
cardinality assertion. Reindexing that fibre as physical integer offsets
on the lifted rectangle remains R2d.2b. No reflection intertwiner, Neumann
inverse, physical B0 or window15 is claimed by this single field formula.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator RealInnerProductSpace

noncomputable section

variable {d M N Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero Nc]

/-- The literal generated average acts by its actual terminal-owner fibre.
This is an equality, not a cardinality estimate or a supplied Q dictionary. -/
theorem CMP99SourceActiveRegionChain.flatExplicitQprime_apply_eq_terminalFibreSum
    {depth : ℕ} {Omega : ActiveGaugeRegion d N}
    (regions : CMP99SourceActiveRegionChain d M N Omega depth) :
    letI : NeZero N := regions.neZero
    ∀ (f : ActiveGaugeZeroCochain Omega (SUNLieCoord Nc))
      (target : regions.terminalSite),
      regions.flatExplicitQprime (Nc := Nc) f target =
        (cmp99SourceBlockAverageWeight M d) ^ depth •
          (∑ source : ActiveGaugeRegion.Site Omega,
            if target = regions.terminalSiteOfFine source then f source else 0) := by
  letI : NeZero N := regions.neZero
  intro f target
  classical
  have hdecomp : regions.flatExplicitQprime (Nc := Nc) f =
      ∑ source : ActiveGaugeRegion.Site Omega,
        regions.flatExplicitQprime (Nc := Nc)
          (singleFinitePiLp source (f source)) := by
    rw [← map_sum, sum_singleFinitePiLp_eq]
  have happ := congrArg
    (fun z : PiLp 2 (fun _ : regions.terminalSite => SUNLieCoord Nc) => z target)
    hdecomp
  simp only [WithLp.ofLp_sum, Finset.sum_apply] at happ
  rw [happ, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro source _
  rw [regions.flatExplicitQprime_single]
  by_cases h : target = regions.terminalSiteOfFine source
  · subst target
    simp only [singleFinitePiLp_self, if_pos rfl, ite_true]
  · rw [singleFinitePiLp_of_ne _ h, if_neg h, smul_zero]

/-- Source-weighted mass action on a complete field, with the coefficient
appearing ONCE. Its output/source owners are the actual generated owners. -/
theorem CMP99SourceActiveRegionChain.flatExplicitWeightedMass_apply_eq_terminalFibreSum
    {depth : ℕ} {Omega : ActiveGaugeRegion d N}
    (regions : CMP99SourceActiveRegionChain d M N Omega depth) :
    letI : NeZero N := regions.neZero
    ∀ (f : ActiveGaugeZeroCochain Omega (SUNLieCoord Nc))
      (target : ActiveGaugeRegion.Site Omega),
      ((regions.flatExplicitWeightedAdjoint (Nc := Nc)).comp
        (regions.flatExplicitQprime (Nc := Nc))) f target =
        (cmp99SourceBlockAverageWeight M d) ^ depth •
          (∑ source : ActiveGaugeRegion.Site Omega,
            if regions.terminalSiteOfFine target = regions.terminalSiteOfFine source
            then f source else 0) := by
  letI : NeZero N := regions.neZero
  intro f target
  rw [ContinuousLinearMap.comp_apply, regions.flatExplicitWeightedAdjoint_apply,
    regions.flatExplicitQprime_apply_eq_terminalFibreSum]

/-- Counting-adjoint mass action on the same complete field. The second
weight is retained explicitly as exponent 2*depth, not silently discarded. -/
theorem CMP99SourceActiveRegionChain.flatExplicitCountingMass_apply_eq_terminalFibreSum
    {depth : ℕ} {Omega : ActiveGaugeRegion d N}
    (regions : CMP99SourceActiveRegionChain d M N Omega depth) :
    letI : NeZero N := regions.neZero
    ∀ (f : ActiveGaugeZeroCochain Omega (SUNLieCoord Nc))
      (target : ActiveGaugeRegion.Site Omega),
      ((regions.flatExplicitQprime (Nc := Nc)).adjoint.comp
        (regions.flatExplicitQprime (Nc := Nc))) f target =
        (cmp99SourceBlockAverageWeight M d) ^ (2 * depth) •
          (∑ source : ActiveGaugeRegion.Site Omega,
            if regions.terminalSiteOfFine target = regions.terminalSiteOfFine source
            then f source else 0) := by
  letI : NeZero N := regions.neZero
  intro f target
  rw [regions.flatExplicitQprime_adjoint_comp_eq]
  change (cmp99SourceBlockAverageWeight M d) ^ depth •
    (((regions.flatExplicitWeightedAdjoint (Nc := Nc)).comp
      (regions.flatExplicitQprime (Nc := Nc))) f target) = _
  rw [regions.flatExplicitWeightedMass_apply_eq_terminalFibreSum, smul_smul]
  congr 1
  rw [← pow_add, two_mul]

end
end YangMills.RG

#print axioms YangMills.RG.CMP99SourceActiveRegionChain.flatExplicitQprime_apply_eq_terminalFibreSum
#print axioms YangMills.RG.CMP99SourceActiveRegionChain.flatExplicitWeightedMass_apply_eq_terminalFibreSum
#print axioms YangMills.RG.CMP99SourceActiveRegionChain.flatExplicitCountingMass_apply_eq_terminalFibreSum
