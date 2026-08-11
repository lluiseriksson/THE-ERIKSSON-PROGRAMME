/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceFlatFullComplexPrecisionStabilizedQprimeStarField

/-!
# Linear packaging of the stabilized flat physical `G Q'^*` field

PRE-VALIDATION: source is present, its `.olean` has not yet been materialized,
and the result has not yet been verified by the Lean compiler.

The sealed arbitrary-source field is linear in its coarse physical source.
This file packages that literal finite Fourier superposition as a
continuous complex-linear map and restates the already proved full-box
equation at the bundled endpoint.

This is still `G Q'^*`, not the inverse `G` itself.  Identification with the
generated physical covariance, interacting/regional transport and a uniform
physical `B0` remain separate downstream obligations.
-/

namespace YangMills.RG

open YangMills Matrix

noncomputable section

variable {d M N' Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero N'] [NeZero Nc]

omit [NeZero d] [NeZero Nc] in
/-- The stabilized one-mode particular solution is additive in its physical
fibre coefficient. -/
theorem cmp99SourceFlatFullComplexPrecisionStabilizedParticularSolution_add
    (ell : FinBox d N') (mass a : ℝ)
    (v w : SUNLieComplexCoord Nc) :
    cmp99SourceFlatFullComplexPrecisionStabilizedParticularSolution
        (d := d) (M := M) (N' := N') (Nc := Nc) ell mass a (v + w) =
      cmp99SourceFlatFullComplexPrecisionStabilizedParticularSolution
          (d := d) (M := M) (N' := N') (Nc := Nc) ell mass a v +
        cmp99SourceFlatFullComplexPrecisionStabilizedParticularSolution
          (d := d) (M := M) (N' := N') (Nc := Nc) ell mass a w := by
  apply (cmp99FlatPhysicalFibreDFTLinearEquiv
    (d := d) (N := M * N') (Nc := Nc)).injective
  rw [map_add]
  funext k
  change cmp99FlatPhysicalFibreDFT
      (cmp99SourceFlatFullComplexPrecisionStabilizedParticularSolution
        ell mass a (v + w)) k =
    cmp99FlatPhysicalFibreDFT
        (cmp99SourceFlatFullComplexPrecisionStabilizedParticularSolution
          ell mass a v) k +
      cmp99FlatPhysicalFibreDFT
        (cmp99SourceFlatFullComplexPrecisionStabilizedParticularSolution
          ell mass a w) k
  by_cases hk : cmp99SourceFlatQprimeCoarseAlias k = ell
  · let output : CMP99SourceFlatQprimeFixedCoarseFibre d M N' ell := ⟨k, hk⟩
    rw [cmp99FlatPhysicalFibreDFT_stabilizedParticularSolution_fixedCoarseFibre
          (d := d) (M := M) (N' := N') (Nc := Nc) ell mass a (v + w) output,
      cmp99FlatPhysicalFibreDFT_stabilizedParticularSolution_fixedCoarseFibre
          (d := d) (M := M) (N' := N') (Nc := Nc) ell mass a v output,
      cmp99FlatPhysicalFibreDFT_stabilizedParticularSolution_fixedCoarseFibre
          (d := d) (M := M) (N' := N') (Nc := Nc) ell mass a w output]
    module
  · rw [cmp99FlatPhysicalFibreDFT_stabilizedParticularSolution_eq_zero_of_coarseAlias_ne
          (d := d) (M := M) (N' := N') (Nc := Nc) ell mass a (v + w) k hk,
      cmp99FlatPhysicalFibreDFT_stabilizedParticularSolution_eq_zero_of_coarseAlias_ne
          (d := d) (M := M) (N' := N') (Nc := Nc) ell mass a v k hk,
      cmp99FlatPhysicalFibreDFT_stabilizedParticularSolution_eq_zero_of_coarseAlias_ne
          (d := d) (M := M) (N' := N') (Nc := Nc) ell mass a w k hk]
    exact (add_zero 0).symm

omit [NeZero d] [NeZero Nc] in
/-- The stabilized one-mode particular solution commutes with complex scalar
multiplication of its physical fibre coefficient. -/
theorem cmp99SourceFlatFullComplexPrecisionStabilizedParticularSolution_smul
    (ell : FinBox d N') (mass a : ℝ) (c : ℂ)
    (v : SUNLieComplexCoord Nc) :
    cmp99SourceFlatFullComplexPrecisionStabilizedParticularSolution
        (d := d) (M := M) (N' := N') (Nc := Nc) ell mass a (c • v) =
      c • cmp99SourceFlatFullComplexPrecisionStabilizedParticularSolution
        (d := d) (M := M) (N' := N') (Nc := Nc) ell mass a v := by
  apply (cmp99FlatPhysicalFibreDFTLinearEquiv
    (d := d) (N := M * N') (Nc := Nc)).injective
  rw [map_smul]
  funext k
  change cmp99FlatPhysicalFibreDFT
      (cmp99SourceFlatFullComplexPrecisionStabilizedParticularSolution
        ell mass a (c • v)) k =
    c • cmp99FlatPhysicalFibreDFT
      (cmp99SourceFlatFullComplexPrecisionStabilizedParticularSolution
        ell mass a v) k
  by_cases hk : cmp99SourceFlatQprimeCoarseAlias k = ell
  · let output : CMP99SourceFlatQprimeFixedCoarseFibre d M N' ell := ⟨k, hk⟩
    rw [cmp99FlatPhysicalFibreDFT_stabilizedParticularSolution_fixedCoarseFibre
          (d := d) (M := M) (N' := N') (Nc := Nc) ell mass a (c • v) output,
      cmp99FlatPhysicalFibreDFT_stabilizedParticularSolution_fixedCoarseFibre
          (d := d) (M := M) (N' := N') (Nc := Nc) ell mass a v output]
    module
  · rw [cmp99FlatPhysicalFibreDFT_stabilizedParticularSolution_eq_zero_of_coarseAlias_ne
          (d := d) (M := M) (N' := N') (Nc := Nc) ell mass a (c • v) k hk,
      cmp99FlatPhysicalFibreDFT_stabilizedParticularSolution_eq_zero_of_coarseAlias_ne
          (d := d) (M := M) (N' := N') (Nc := Nc) ell mass a v k hk]
    exact (smul_zero c).symm

omit [NeZero d] [NeZero Nc] in
/-- The finite arbitrary-source `G Q'^*` field is additive. -/
theorem cmp99SourceFlatFullComplexPrecisionStabilizedQprimeStarField_add
    (mass a : ℝ)
    (eta zeta : FinBox d N' → SUNLieComplexCoord Nc) :
    cmp99SourceFlatFullComplexPrecisionStabilizedQprimeStarField
        (d := d) (M := M) (N' := N') (Nc := Nc) mass a (eta + zeta) =
      cmp99SourceFlatFullComplexPrecisionStabilizedQprimeStarField
          (d := d) (M := M) (N' := N') (Nc := Nc) mass a eta +
        cmp99SourceFlatFullComplexPrecisionStabilizedQprimeStarField
          (d := d) (M := M) (N' := N') (Nc := Nc) mass a zeta := by
  unfold cmp99SourceFlatFullComplexPrecisionStabilizedQprimeStarField
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro ell _
  have hDFT : cmp99FlatPhysicalFibreDFT (eta + zeta) ell =
      cmp99FlatPhysicalFibreDFT eta ell +
        cmp99FlatPhysicalFibreDFT zeta ell := by
    change (cmp99FlatPhysicalFibreDFTLinearEquiv
        (d := d) (N := N') (Nc := Nc)) (eta + zeta) ell =
      (cmp99FlatPhysicalFibreDFTLinearEquiv
          (d := d) (N := N') (Nc := Nc)) eta ell +
        (cmp99FlatPhysicalFibreDFTLinearEquiv
          (d := d) (N := N') (Nc := Nc)) zeta ell
    exact congrFun
      ((cmp99FlatPhysicalFibreDFTLinearEquiv
        (d := d) (N := N') (Nc := Nc)).map_add eta zeta) ell
  rw [hDFT, smul_add,
    cmp99SourceFlatFullComplexPrecisionStabilizedParticularSolution_add
      (d := d) (M := M) (N' := N') (Nc := Nc)]

omit [NeZero d] [NeZero Nc] in
/-- The finite arbitrary-source `G Q'^*` field commutes with complex scalar
multiplication. -/
theorem cmp99SourceFlatFullComplexPrecisionStabilizedQprimeStarField_smul
    (mass a : ℝ) (c : ℂ)
    (eta : FinBox d N' → SUNLieComplexCoord Nc) :
    cmp99SourceFlatFullComplexPrecisionStabilizedQprimeStarField
        (d := d) (M := M) (N' := N') (Nc := Nc) mass a (c • eta) =
      c • cmp99SourceFlatFullComplexPrecisionStabilizedQprimeStarField
        (d := d) (M := M) (N' := N') (Nc := Nc) mass a eta := by
  unfold cmp99SourceFlatFullComplexPrecisionStabilizedQprimeStarField
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro ell _
  have hDFT : cmp99FlatPhysicalFibreDFT (c • eta) ell =
      c • cmp99FlatPhysicalFibreDFT eta ell := by
    change (cmp99FlatPhysicalFibreDFTLinearEquiv
        (d := d) (N := N') (Nc := Nc)) (c • eta) ell =
      c • (cmp99FlatPhysicalFibreDFTLinearEquiv
        (d := d) (N := N') (Nc := Nc)) eta ell
    exact congrFun
      ((cmp99FlatPhysicalFibreDFTLinearEquiv
        (d := d) (N := N') (Nc := Nc)).map_smul c eta) ell
  rw [hDFT]
  rw [show ((((N' : ℕ) : ℂ) ^ d)⁻¹ •
      (c • cmp99FlatPhysicalFibreDFT eta ell)) =
        c • ((((N' : ℕ) : ℂ) ^ d)⁻¹ •
          cmp99FlatPhysicalFibreDFT eta ell) by module]
  exact
    cmp99SourceFlatFullComplexPrecisionStabilizedParticularSolution_smul
      (d := d) (M := M) (N' := N') (Nc := Nc) ell mass a c _

/-- Complex-linear map underlying the stabilized full-box `G Q'^*` field. -/
noncomputable def
    cmp99SourceFlatFullComplexPrecisionStabilizedQprimeStarFieldLM
    (mass a : ℝ) :
    (FinBox d N' → SUNLieComplexCoord Nc) →ₗ[ℂ]
      (FinBox d (M * N') → SUNLieComplexCoord Nc) where
  toFun := cmp99SourceFlatFullComplexPrecisionStabilizedQprimeStarField
    (d := d) (M := M) (N' := N') (Nc := Nc) mass a
  map_add' :=
    cmp99SourceFlatFullComplexPrecisionStabilizedQprimeStarField_add
      (d := d) (M := M) (N' := N') (Nc := Nc) mass a
  map_smul' :=
    cmp99SourceFlatFullComplexPrecisionStabilizedQprimeStarField_smul
      (d := d) (M := M) (N' := N') (Nc := Nc) mass a

/-- Continuous complex-linear packaging of the internally constructed
stabilized full-box `G Q'^*` field. -/
noncomputable def
    cmp99SourceFlatFullComplexPrecisionStabilizedQprimeStarFieldCLM
    (mass a : ℝ) :
    (FinBox d N' → SUNLieComplexCoord Nc) →L[ℂ]
      (FinBox d (M * N') → SUNLieComplexCoord Nc) :=
  LinearMap.toContinuousLinearMap
    (cmp99SourceFlatFullComplexPrecisionStabilizedQprimeStarFieldLM
      (d := d) (M := M) (N' := N') (Nc := Nc) mass a)

omit [NeZero d] [NeZero Nc] in
@[simp] theorem
    cmp99SourceFlatFullComplexPrecisionStabilizedQprimeStarFieldCLM_apply
    (mass a : ℝ) (eta : FinBox d N' → SUNLieComplexCoord Nc) :
    cmp99SourceFlatFullComplexPrecisionStabilizedQprimeStarFieldCLM
        (d := d) (M := M) (N' := N') (Nc := Nc) mass a eta =
      cmp99SourceFlatFullComplexPrecisionStabilizedQprimeStarField
        (d := d) (M := M) (N' := N') (Nc := Nc) mass a eta := rfl

/-- Bundled endpoint: the literal precision sends the internally constructed
continuous-linear `G Q'^*` field exactly to the coefficient-one weighted
adjoint of every coarse source. -/
theorem cmp99SourceFlatFullComplexPrecisionAction_stabilizedQprimeStarFieldCLM
    (mass a : ℝ) (eta : FinBox d N' → SUNLieComplexCoord Nc)
    (hfine : ∀ ell : FinBox d N',
      ∀ k : CMP99SourceFlatQprimeFixedCoarseFibre d M N' ell,
        k ≠ cmp99SourceFlatQprimePhysicalCentralAliasIndex
            (d := d) (M := M) (N' := N') ell →
          cmp99SourceFlatQprimePhysicalFineSymbol mass k.1 ≠ 0)
    (hstabilized : ∀ ell : FinBox d N',
      cmp89Eq249CentralStabilizedAliasDenominator d M 1 mass a
        (cmp99SourceFlatQprimeCoarseAmplitudeBaseMomentum ell) ≠ 0) :
    cmp99SourceFlatFullComplexPrecisionAction
        (d := d) (M := M) (N' := N') (Nc := Nc) mass a
        (cmp99SourceFlatFullComplexPrecisionStabilizedQprimeStarFieldCLM
          (d := d) (M := M) (N' := N') (Nc := Nc) mass a eta) =
      cmp99SourceFlatFullComplexWeightedAdjoint
        (d := d) (M := M) (N' := N') (Nc := Nc) eta := by
  exact cmp99SourceFlatFullComplexPrecisionAction_stabilizedQprimeStarField
    (d := d) (M := M) (N' := N') (Nc := Nc) mass a eta hfine hstabilized

end

end YangMills.RG
