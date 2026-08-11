/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceFlatGeneratedQprimeTerminalOwner

/-!
PRE-VALIDATION: source is present, its `.olean` has not yet been materialized,
and the result has not yet been verified by the Lean compiler.

# Direct terminal-owner kernels for the canonical flat generated `Q'`

The terminal-owner seal states its kernels through equality in the dependent
terminal-site type of an arbitrary source chain.  On the canonical iterated
lift, that equality is exactly equality of the literal coordinatewise
order-`M^depth` owner `cmp99GeneratedTerminalBlockSite`.

This file performs only that exact dictionary step.  It does not claim that a
terminal fibre of an arbitrary active region has full cardinality
`(M^depth)^d`: boundary-truncated active regions need only satisfy the sealed
upper bound.  It also does not identify CMP99 strata, match a precision,
construct an inverse or prove a Green bound.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator RealInnerProductSpace

noncomputable section

variable {d M N Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero N] [NeZero Nc]

/-- Equality of dependent terminal owners on the canonical lifted chain is
exactly equality of the literal coordinatewise order-`M^depth` owners. -/
theorem cmp99SourceIteratedLift_terminalOwner_eq_iff_generatedTerminalBlockSite_eq
    (Omega : ActiveGaugeRegion d N) (depth : ℕ)
    (target source : ActiveGaugeRegion.Site
      (cmp99IteratedLiftActiveRegion (M := M) Omega depth)) :
    let regions :=
      cmp99SourceIteratedLiftActiveRegionChain (M := M) Omega depth
    regions.terminalSiteOfFine target = regions.terminalSiteOfFine source ↔
      cmp99GeneratedTerminalBlockSite M N depth target.1 =
        cmp99GeneratedTerminalBlockSite M N depth source.1 := by
  let regions :=
    cmp99SourceIteratedLiftActiveRegionChain (M := M) Omega depth
  rw [← regions.sameTerminalBlock_iff_terminalSiteOfFine_eq,
    cmp99SourceIteratedLift_sameTerminalBlock_iff]

/-- Exact direct-owner kernel of the source-weighted flat generated mass on
the canonical iterated lift. -/
theorem cmp99SourceIteratedLift_flatExplicitWeightedMass_single_apply
    (Omega : ActiveGaugeRegion d N) (depth : ℕ) :
    let regions :=
      cmp99SourceIteratedLiftActiveRegionChain (M := M) Omega depth
    letI : NeZero (cmp99RegionalLatticeSize M N depth) := regions.neZero
    ∀ (source target : ActiveGaugeRegion.Site
        (cmp99IteratedLiftActiveRegion (M := M) Omega depth))
      (v : SUNLieCoord Nc),
      ((regions.flatExplicitWeightedAdjoint (Nc := Nc)).comp
          (regions.flatExplicitQprime (Nc := Nc)))
            (singleFinitePiLp source v) target =
        if cmp99GeneratedTerminalBlockSite M N depth target.1 =
            cmp99GeneratedTerminalBlockSite M N depth source.1 then
          (cmp99SourceBlockAverageWeight M d) ^ depth • v
        else 0 := by
  let regions :=
    cmp99SourceIteratedLiftActiveRegionChain (M := M) Omega depth
  letI : NeZero (cmp99RegionalLatticeSize M N depth) := regions.neZero
  intro source target v
  rw [regions.flatExplicitWeightedMass_single_apply]
  exact if_congr
    (cmp99SourceIteratedLift_terminalOwner_eq_iff_generatedTerminalBlockSite_eq
      (M := M) Omega depth target source)
    rfl rfl

/-- Exact direct-owner kernel of Lean's counting-adjoint flat generated mass
on the canonical iterated lift. -/
theorem cmp99SourceIteratedLift_flatExplicitCountingMass_single_apply
    (Omega : ActiveGaugeRegion d N) (depth : ℕ) :
    let regions :=
      cmp99SourceIteratedLiftActiveRegionChain (M := M) Omega depth
    letI : NeZero (cmp99RegionalLatticeSize M N depth) := regions.neZero
    ∀ (source target : ActiveGaugeRegion.Site
        (cmp99IteratedLiftActiveRegion (M := M) Omega depth))
      (v : SUNLieCoord Nc),
      ((regions.flatExplicitQprime (Nc := Nc)).adjoint.comp
          (regions.flatExplicitQprime (Nc := Nc)))
            (singleFinitePiLp source v) target =
        if cmp99GeneratedTerminalBlockSite M N depth target.1 =
            cmp99GeneratedTerminalBlockSite M N depth source.1 then
          (cmp99SourceBlockAverageWeight M d) ^ (2 * depth) • v
        else 0 := by
  let regions :=
    cmp99SourceIteratedLiftActiveRegionChain (M := M) Omega depth
  letI : NeZero (cmp99RegionalLatticeSize M N depth) := regions.neZero
  intro source target v
  rw [regions.flatExplicitCountingMass_single_apply]
  exact if_congr
    (cmp99SourceIteratedLift_terminalOwner_eq_iff_generatedTerminalBlockSite_eq
      (M := M) Omega depth target source)
    rfl rfl

end

end YangMills.RG
