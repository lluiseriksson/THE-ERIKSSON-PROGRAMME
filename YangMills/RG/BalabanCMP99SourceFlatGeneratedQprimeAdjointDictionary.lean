/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceFlatGeneratedQprimeRecursion

/-!
PRE-VALIDATION: source is present, its `.olean` has not yet been materialized,
and the result has not yet been verified by the Lean compiler.

# Counting/source-weighted adjoint dictionary for the flat generated `Q'`

CMP99 uses the lattice-spacing Hilbert products, whose one-step adjoint is
the coefficient-one synthesis.  Lean's counting-space adjoint instead keeps
one factor `M^{-d}`.  This file records that conversion first for one literal
flat scale and then for the complete typed generated recursion.

The final theorem rewrites the counting-space mass `Q'^* Q'` with the same
explicit factor.  No terminal-block collapse, source-stratum identification,
inverse, Green bound, or precision identification is made here.
-/

namespace YangMills.RG

open YangMills

noncomputable section

variable {d M N Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero N] [NeZero Nc]

omit [NeZero d] [NeZero Nc] in
/-- At one flat scale, the counting-space Hilbert adjoint is exactly one
source averaging weight times the coefficient-one weighted adjoint. -/
theorem cmp99SourceFlatRealBlockAverageCLM_adjoint_eq_weight_smul
    {N' : ℕ} [NeZero N'] (Omega : ActiveGaugeRegion d (M * N'))
    (hOmega : Omega.BlockSaturated) :
    (cmp99SourceFlatRealBlockAverageCLM
        (Nc := Nc) Omega).adjoint =
      cmp99SourceBlockAverageWeight M d •
        cmp99SourceFlatRealBlockWeightedAdjointCLM Omega hOmega := by
  change
    (cmp99SourceTransportedBlockAverageCLM Omega
      (cmp99SourceFlatRealTransport
        (d := d) (M := M) (N' := N') (Nc := Nc))).adjoint =
      cmp99SourceBlockAverageWeight M d •
        cmp99SourceTransportedBlockWeightedAdjointCLM Omega hOmega
          (cmp99SourceFlatRealTransport
            (d := d) (M := M) (N' := N') (Nc := Nc))
  rw [cmp99SourceTransportedBlockWeightedAdjointCLM_eq_smul_adjoint]
  apply ContinuousLinearMap.ext
  intro eta
  simp only [ContinuousLinearMap.smul_apply, smul_smul]
  rw [cmp99SourceBlockAverageWeight_mul_card, one_smul]

/-- The complete generated counting adjoint retains exactly one factor
`M^{-d}` per recursive scale.  The reverse operator is the literal
coefficient-one synthesis recursion paired with the same region chain. -/
theorem CMP99SourceActiveRegionChain.flatExplicitQprime_adjoint_eq_weight_pow_smul
    {depth : ℕ} {Omega : ActiveGaugeRegion d N}
    (regions : CMP99SourceActiveRegionChain d M N Omega depth) :
    letI : NeZero N := regions.neZero
    (regions.flatExplicitQprime (Nc := Nc)).adjoint =
      (cmp99SourceBlockAverageWeight M d) ^ depth •
        regions.flatExplicitWeightedAdjoint (Nc := Nc) := by
  letI : NeZero N := regions.neZero
  induction regions with
  | stop Omega =>
      simp only [CMP99SourceActiveRegionChain.flatExplicitQprime,
        CMP99SourceActiveRegionChain.flatExplicitWeightedAdjoint,
        pow_zero, one_smul]
      apply ContinuousLinearMap.ext
      intro eta
      apply ext_inner_right ℝ
      intro phi
      rw [ContinuousLinearMap.adjoint_inner_left]
      rfl
  | @step N' depth _ Omega hOmega tail ih =>
      letI : NeZero (M * N') := inferInstance
      change
        ((tail.flatExplicitQprime (Nc := Nc)).comp
          (cmp99SourceFlatRealBlockAverageCLM Omega)).adjoint =
        (cmp99SourceBlockAverageWeight M d) ^ (depth + 1) •
          ((cmp99SourceFlatRealBlockWeightedAdjointCLM Omega hOmega).comp
            (tail.flatExplicitWeightedAdjoint (Nc := Nc)))
      rw [ContinuousLinearMap.adjoint_comp, ih,
        cmp99SourceFlatRealBlockAverageCLM_adjoint_eq_weight_smul
          Omega hOmega]
      apply ContinuousLinearMap.ext
      intro eta
      simp only [ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.smul_apply, map_smul, smul_smul, pow_succ]

omit [NeZero N] in
/-- Consequently the literal counting-space mass `Q'^* Q'` is the
source-weighted mass with the same visible recursive volume factor. -/
theorem CMP99SourceActiveRegionChain.flatExplicitQprime_adjoint_comp_eq
    {depth : ℕ} {Omega : ActiveGaugeRegion d N}
    (regions : CMP99SourceActiveRegionChain d M N Omega depth) :
    letI : NeZero N := regions.neZero
    (regions.flatExplicitQprime (Nc := Nc)).adjoint.comp
        (regions.flatExplicitQprime (Nc := Nc)) =
      (cmp99SourceBlockAverageWeight M d) ^ depth •
        ((regions.flatExplicitWeightedAdjoint (Nc := Nc)).comp
          (regions.flatExplicitQprime (Nc := Nc))) := by
  letI : NeZero N := regions.neZero
  rw [regions.flatExplicitQprime_adjoint_eq_weight_pow_smul]
  apply ContinuousLinearMap.ext
  intro phi
  simp only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smul_apply]

end

end YangMills.RG
