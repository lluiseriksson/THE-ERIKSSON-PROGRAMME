/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceFlatGeneratedQprimeRecursion
import YangMills.RG.BalabanCMP99SourceFlatPhysicalComplexWeightedAdjoint

/-!
# Complexification of the generated flat CMP99 `Q'` recursion

The generated flat physical tower is a typed multiscale recursion, not one
global terminal block average.  This file constructs the same recursion on
the explicit complexified Lie-coordinate fibre and proves that both the
forward average and the reverse coefficient-one weighted adjoint commute with
pointwise complexification at every scale.

No complex operator family is supplied by the caller.  The recursion is built
internally from the already sealed one-step flat complex average and weighted
adjoint.  Honest scope: this does not identify different source strata,
replace the recursively generated `Q'_r` by one terminal average, match the
generated real precision with the separately reconstructed flat complex
precision, construct an inverse, or produce a regional Green bound.
-/

namespace YangMills.RG

open YangMills

noncomputable section

variable {d M N Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero N] [NeZero Nc]

/-- Pointwise complexification on a finite `PiLp` field.  The index type is
kept explicit so the terminal coordinate type of a dependent region chain is
not replaced by a caller-supplied equivalence. -/
noncomputable def cmp99FinitePiLpSUNLieCoordComplexificationCLM
    (ι : Type) [Fintype ι] [DecidableEq ι] :
    PiLp 2 (fun _ : ι => SUNLieCoord Nc) →L[ℝ]
      PiLp 2 (fun _ : ι => SUNLieComplexCoord Nc) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun phi => WithLp.toLp 2 fun i =>
        cmp99SUNLieCoordComplexificationLM Nc (phi i)
      map_add' := fun phi psi => by
        apply WithLp.ofLp_injective
        funext i
        exact (cmp99SUNLieCoordComplexificationLM Nc).map_add (phi i) (psi i)
      map_smul' := fun r phi => by
        apply WithLp.ofLp_injective
        funext i
        exact (cmp99SUNLieCoordComplexificationLM Nc).map_smul r (phi i) }

omit [NeZero d] [NeZero M] [NeZero N] [NeZero Nc] in
@[simp] theorem cmp99FinitePiLpSUNLieCoordComplexificationCLM_apply
    (ι : Type) [Fintype ι] [DecidableEq ι]
    (phi : PiLp 2 (fun _ : ι => SUNLieCoord Nc)) (i : ι) :
    cmp99FinitePiLpSUNLieCoordComplexificationCLM (Nc := Nc) ι phi i =
      cmp99SUNLieCoordComplexificationLM Nc (phi i) := rfl

/-- The explicit one-step complex flat average commutes with the explicit
real flat average, with no adjoint model left as caller data. -/
theorem cmp99SourceFlatComplexBlockAverage_commutes_real_explicit
    {N' : ℕ} [NeZero N'] (Omega : ActiveGaugeRegion d (M * N'))
    (phi : ActiveGaugeZeroCochain Omega (SUNLieCoord Nc)) :
    cmp99SourceFlatComplexBlockAverageCLM Omega
        (cmp99ActiveGaugeZeroCochainComplexificationCLM Omega phi) =
      cmp99ActiveGaugeZeroCochainComplexificationCLM
        (cmp99ActiveCoarseRegion (M := M) (N' := N') Omega)
        (cmp99SourceFlatRealBlockAverageCLM Omega phi) := by
  have h := cmp99SourceFlatComplexBlockAverage_commutes_complexification
    Omega (matrixSUNAdjointModel Nc) phi
  rw [cmp99SourceTransportedBlockAverageCLM_flat_eq_explicit] at h
  exact h

/-- The explicit one-step coefficient-one complex synthesis commutes with
the paired explicit real synthesis. -/
theorem cmp99SourceFlatComplexBlockWeightedAdjoint_commutes_real_explicit
    {N' : ℕ} [NeZero N'] (Omega : ActiveGaugeRegion d (M * N'))
    (hOmega : Omega.BlockSaturated)
    (eta : ActiveGaugeZeroCochain
      (cmp99ActiveCoarseRegion (M := M) (N' := N') Omega)
      (SUNLieCoord Nc)) :
    cmp99SourceFlatComplexBlockWeightedAdjointCLM Omega hOmega
        (cmp99ActiveGaugeZeroCochainComplexificationCLM
          (cmp99ActiveCoarseRegion (M := M) (N' := N') Omega) eta) =
      cmp99ActiveGaugeZeroCochainComplexificationCLM Omega
        (cmp99SourceFlatRealBlockWeightedAdjointCLM Omega hOmega eta) := by
  have h :=
    cmp99SourceFlatComplexBlockWeightedAdjoint_commutes_complexification
      Omega hOmega (matrixSUNAdjointModel Nc) eta
  rw [cmp99SourceTransportedBlockWeightedAdjointCLM_flat_eq_explicit] at h
  exact h

/-- The complete explicit flat `Q'_r` recursion on the complexified physical
fibre.  Its dependent terminal coordinate type is inherited from the same
literal active-region chain as the generated real recursion. -/
noncomputable def CMP99SourceActiveRegionChain.flatExplicitComplexQprime
    {N depth : ℕ} {Omega : ActiveGaugeRegion d N}
    (regions : CMP99SourceActiveRegionChain d M N Omega depth) :
    letI : NeZero N := regions.neZero
    ActiveGaugeZeroCochain Omega (SUNLieComplexCoord Nc) →L[ℝ]
      PiLp 2 (fun _ : regions.terminalSite => SUNLieComplexCoord Nc) := by
  letI : NeZero N := regions.neZero
  induction regions with
  | stop Omega =>
      exact ContinuousLinearMap.id ℝ _
  | @step N' depth _ Omega hOmega tail ih =>
      letI : NeZero (M * N') := inferInstance
      exact ih.comp (cmp99SourceFlatComplexBlockAverageCLM Omega)

/-- The reverse coefficient-one complex synthesis recursion paired with
`flatExplicitComplexQprime`. -/
noncomputable def
    CMP99SourceActiveRegionChain.flatExplicitComplexWeightedAdjoint
    {N depth : ℕ} {Omega : ActiveGaugeRegion d N}
    (regions : CMP99SourceActiveRegionChain d M N Omega depth) :
    letI : NeZero N := regions.neZero
    PiLp 2 (fun _ : regions.terminalSite => SUNLieComplexCoord Nc) →L[ℝ]
      ActiveGaugeZeroCochain Omega (SUNLieComplexCoord Nc) := by
  letI : NeZero N := regions.neZero
  induction regions with
  | stop Omega =>
      exact ContinuousLinearMap.id ℝ _
  | @step N' depth _ Omega hOmega tail ih =>
      letI : NeZero (M * N') := inferInstance
      exact (cmp99SourceFlatComplexBlockWeightedAdjointCLM Omega hOmega).comp ih

/-- The complete internally constructed complex average recursion commutes
with pointwise complexification of the explicit generated real recursion. -/
theorem
    CMP99SourceActiveRegionChain.flatExplicitComplexQprime_commutes_complexification
    {N depth : ℕ} {Omega : ActiveGaugeRegion d N}
    (regions : CMP99SourceActiveRegionChain d M N Omega depth) :
    letI : NeZero N := regions.neZero
    ∀ phi : ActiveGaugeZeroCochain Omega (SUNLieCoord Nc),
      regions.flatExplicitComplexQprime
          (cmp99ActiveGaugeZeroCochainComplexificationCLM Omega phi) =
        cmp99FinitePiLpSUNLieCoordComplexificationCLM
          (Nc := Nc) regions.terminalSite
          (regions.flatExplicitQprime phi) := by
  letI : NeZero N := regions.neZero
  induction regions with
  | stop Omega =>
      intro phi
      rfl
  | @step N' depth _ Omega hOmega tail ih =>
      intro phi
      change
        tail.flatExplicitComplexQprime
            (cmp99SourceFlatComplexBlockAverageCLM Omega
              (cmp99ActiveGaugeZeroCochainComplexificationCLM Omega phi)) =
          cmp99FinitePiLpSUNLieCoordComplexificationCLM
            (Nc := Nc) tail.terminalSite
            (tail.flatExplicitQprime
              (cmp99SourceFlatRealBlockAverageCLM Omega phi))
      rw [cmp99SourceFlatComplexBlockAverage_commutes_real_explicit]
      exact ih _

/-- The complete internally constructed reverse complex synthesis likewise
commutes with pointwise complexification of the generated real synthesis. -/
theorem
    CMP99SourceActiveRegionChain.flatExplicitComplexWeightedAdjoint_commutes_complexification
    {N depth : ℕ} {Omega : ActiveGaugeRegion d N}
    (regions : CMP99SourceActiveRegionChain d M N Omega depth) :
    letI : NeZero N := regions.neZero
    ∀ eta : PiLp 2 (fun _ : regions.terminalSite => SUNLieCoord Nc),
      regions.flatExplicitComplexWeightedAdjoint
          (cmp99FinitePiLpSUNLieCoordComplexificationCLM
            (Nc := Nc) regions.terminalSite eta) =
        cmp99ActiveGaugeZeroCochainComplexificationCLM Omega
          (regions.flatExplicitWeightedAdjoint eta) := by
  letI : NeZero N := regions.neZero
  induction regions with
  | stop Omega =>
      intro eta
      rfl
  | @step N' depth _ Omega hOmega tail ih =>
      intro eta
      change
        cmp99SourceFlatComplexBlockWeightedAdjointCLM Omega hOmega
            (tail.flatExplicitComplexWeightedAdjoint
              (cmp99FinitePiLpSUNLieCoordComplexificationCLM
                (Nc := Nc) tail.terminalSite eta)) =
          cmp99ActiveGaugeZeroCochainComplexificationCLM Omega
            (cmp99SourceFlatRealBlockWeightedAdjointCLM Omega hOmega
              (tail.flatExplicitWeightedAdjoint eta))
      rw [ih eta]
      exact
        cmp99SourceFlatComplexBlockWeightedAdjoint_commutes_real_explicit
          Omega hOmega _

end

end YangMills.RG
