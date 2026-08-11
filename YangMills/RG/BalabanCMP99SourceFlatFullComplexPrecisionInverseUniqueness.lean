/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceFlatFullComplexPrecisionStabilizedQprimeStarCLM

/-!
# Inverse uniqueness for the stabilized flat physical `G Q'^*` field

PRE-VALIDATION: source is present, its `.olean` has not yet been materialized,
and the result has not yet been verified by the Lean compiler.

This file packages the literal full-box precision and coefficient-one
weighted adjoint as continuous complex-linear maps.  The already constructed
stabilized field then satisfies the bundled equation `K H = Q'^*`.

If a left inverse `G` of this same literal `K` is supplied, inverse uniqueness
identifies `H` with `G Q'^*` internally.  The hypothesis is an inverse law,
not the desired equality.  No identification with the real generated
regional precision, its covariance, or its physical parameters is claimed
here.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped BigOperators

noncomputable section

variable {d M N' Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero N'] [NeZero Nc]

omit [NeZero d] [NeZero Nc] in
/-- The literal full-box complex precision is complex homogeneous. -/
theorem cmp99SourceFlatFullComplexPrecisionAction_smul
    (mass a : ℝ) (c : ℂ)
    (phi : FinBox d (M * N') → SUNLieComplexCoord Nc) :
    cmp99SourceFlatFullComplexPrecisionAction mass a (c • phi) =
      c • cmp99SourceFlatFullComplexPrecisionAction mass a phi := by
  funext x
  have hq :
      cmp99SourceFlatFullComplexQprimeMass (c • phi) x =
        c • cmp99SourceFlatFullComplexQprimeMass phi x := by
    unfold cmp99SourceFlatFullComplexQprimeMass
    rw [cmp99SourceFlatComplexBlockWeightedAdjointCLM_apply,
      cmp99SourceFlatComplexBlockAverageCLM_apply]
    simp only [cmp99SourceFlatFullActiveComplexField_apply, Pi.smul_apply]
    rw [← Finset.smul_sum]
    exact smul_comm _ _ _
  have hstencil :
      cmp99FlatPeriodicComplexFibreStencil (c • phi) x =
        c • cmp99FlatPeriodicComplexFibreStencil phi x := by
    unfold cmp99FlatPeriodicComplexFibreStencil
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp only [Pi.smul_apply]
    module
  unfold cmp99SourceFlatFullComplexPrecisionAction
  rw [hq, hstencil]
  simp only [Pi.smul_apply]
  module

/-- Complex-linear packaging of the literal full-box precision. -/
noncomputable def cmp99SourceFlatFullComplexPrecisionLM
    (mass a : ℝ) :
    (FinBox d (M * N') → SUNLieComplexCoord Nc) →ₗ[ℂ]
      (FinBox d (M * N') → SUNLieComplexCoord Nc) where
  toFun := cmp99SourceFlatFullComplexPrecisionAction mass a
  map_add' := cmp99SourceFlatFullComplexPrecisionAction_add mass a
  map_smul' := cmp99SourceFlatFullComplexPrecisionAction_smul mass a

/-- Continuous complex-linear packaging of the literal full-box precision. -/
noncomputable def cmp99SourceFlatFullComplexPrecisionCLM
    (mass a : ℝ) :
    (FinBox d (M * N') → SUNLieComplexCoord Nc) →L[ℂ]
      (FinBox d (M * N') → SUNLieComplexCoord Nc) :=
  LinearMap.toContinuousLinearMap
    (cmp99SourceFlatFullComplexPrecisionLM
      (d := d) (M := M) (N' := N') (Nc := Nc) mass a)

omit [NeZero d] [NeZero Nc] in
@[simp] theorem cmp99SourceFlatFullComplexPrecisionCLM_apply
    (mass a : ℝ) (phi : FinBox d (M * N') → SUNLieComplexCoord Nc) :
    cmp99SourceFlatFullComplexPrecisionCLM
        (d := d) (M := M) (N' := N') (Nc := Nc) mass a phi =
      cmp99SourceFlatFullComplexPrecisionAction mass a phi := rfl

omit [NeZero d] [NeZero Nc] in
/-- The coefficient-one full-box weighted adjoint is additive. -/
theorem cmp99SourceFlatFullComplexWeightedAdjoint_add
    (eta zeta : FinBox d N' → SUNLieComplexCoord Nc) :
    cmp99SourceFlatFullComplexWeightedAdjoint
        (d := d) (M := M) (N' := N') (Nc := Nc) (eta + zeta) =
      cmp99SourceFlatFullComplexWeightedAdjoint
          (d := d) (M := M) (N' := N') (Nc := Nc) eta +
        cmp99SourceFlatFullComplexWeightedAdjoint
          (d := d) (M := M) (N' := N') (Nc := Nc) zeta := by
  funext x
  simp

omit [NeZero d] [NeZero Nc] in
/-- The coefficient-one full-box weighted adjoint is complex homogeneous. -/
theorem cmp99SourceFlatFullComplexWeightedAdjoint_smul
    (c : ℂ) (eta : FinBox d N' → SUNLieComplexCoord Nc) :
    cmp99SourceFlatFullComplexWeightedAdjoint
        (d := d) (M := M) (N' := N') (Nc := Nc) (c • eta) =
      c • cmp99SourceFlatFullComplexWeightedAdjoint
        (d := d) (M := M) (N' := N') (Nc := Nc) eta := by
  funext x
  simp

/-- Complex-linear packaging of the literal coefficient-one `Q'^*`. -/
noncomputable def cmp99SourceFlatFullComplexWeightedAdjointLM :
    (FinBox d N' → SUNLieComplexCoord Nc) →ₗ[ℂ]
      (FinBox d (M * N') → SUNLieComplexCoord Nc) where
  toFun := cmp99SourceFlatFullComplexWeightedAdjoint
    (d := d) (M := M) (N' := N') (Nc := Nc)
  map_add' := cmp99SourceFlatFullComplexWeightedAdjoint_add
    (d := d) (M := M) (N' := N') (Nc := Nc)
  map_smul' := cmp99SourceFlatFullComplexWeightedAdjoint_smul
    (d := d) (M := M) (N' := N') (Nc := Nc)

/-- Continuous complex-linear packaging of the literal coefficient-one
`Q'^*`. -/
noncomputable def cmp99SourceFlatFullComplexWeightedAdjointCLM :
    (FinBox d N' → SUNLieComplexCoord Nc) →L[ℂ]
      (FinBox d (M * N') → SUNLieComplexCoord Nc) :=
  LinearMap.toContinuousLinearMap
    (cmp99SourceFlatFullComplexWeightedAdjointLM
      (d := d) (M := M) (N' := N') (Nc := Nc))

omit [NeZero d] [NeZero Nc] in
@[simp] theorem cmp99SourceFlatFullComplexWeightedAdjointCLM_apply
    (eta : FinBox d N' → SUNLieComplexCoord Nc) :
    cmp99SourceFlatFullComplexWeightedAdjointCLM
        (d := d) (M := M) (N' := N') (Nc := Nc) eta =
      cmp99SourceFlatFullComplexWeightedAdjoint
        (d := d) (M := M) (N' := N') (Nc := Nc) eta := rfl

/-- Bundled form of the exact arbitrary-source equation `K H = Q'^*`. -/
theorem cmp99SourceFlatFullComplexPrecisionCLM_comp_stabilizedFieldCLM
    (mass a : ℝ)
    (hfine : ∀ ell : FinBox d N',
      ∀ k : CMP99SourceFlatQprimeFixedCoarseFibre d M N' ell,
        k ≠ cmp99SourceFlatQprimePhysicalCentralAliasIndex
            (d := d) (M := M) (N' := N') ell →
          cmp99SourceFlatQprimePhysicalFineSymbol mass k.1 ≠ 0)
    (hstabilized : ∀ ell : FinBox d N',
      cmp89Eq249CentralStabilizedAliasDenominator d M 1 mass a
        (cmp99SourceFlatQprimeCoarseAmplitudeBaseMomentum ell) ≠ 0) :
    (cmp99SourceFlatFullComplexPrecisionCLM
        (d := d) (M := M) (N' := N') (Nc := Nc) mass a).comp
      (cmp99SourceFlatFullComplexPrecisionStabilizedQprimeStarFieldCLM
        (d := d) (M := M) (N' := N') (Nc := Nc) mass a) =
      cmp99SourceFlatFullComplexWeightedAdjointCLM
        (d := d) (M := M) (N' := N') (Nc := Nc) := by
  apply ContinuousLinearMap.ext
  intro eta
  exact
    cmp99SourceFlatFullComplexPrecisionAction_stabilizedQprimeStarFieldCLM
      (d := d) (M := M) (N' := N') (Nc := Nc)
      mass a eta hfine hstabilized

/-- Inverse uniqueness: any left inverse of the same literal full-box
precision identifies the internally constructed field with `G Q'^*`. -/
theorem cmp99SourceFlatFullComplexPrecisionStabilizedFieldCLM_eq_inverse_comp
    (mass a : ℝ)
    (G : (FinBox d (M * N') → SUNLieComplexCoord Nc) →L[ℂ]
      (FinBox d (M * N') → SUNLieComplexCoord Nc))
    (hGK : G.comp
        (cmp99SourceFlatFullComplexPrecisionCLM
          (d := d) (M := M) (N' := N') (Nc := Nc) mass a) =
      ContinuousLinearMap.id ℂ _)
    (hfine : ∀ ell : FinBox d N',
      ∀ k : CMP99SourceFlatQprimeFixedCoarseFibre d M N' ell,
        k ≠ cmp99SourceFlatQprimePhysicalCentralAliasIndex
            (d := d) (M := M) (N' := N') ell →
          cmp99SourceFlatQprimePhysicalFineSymbol mass k.1 ≠ 0)
    (hstabilized : ∀ ell : FinBox d N',
      cmp89Eq249CentralStabilizedAliasDenominator d M 1 mass a
        (cmp99SourceFlatQprimeCoarseAmplitudeBaseMomentum ell) ≠ 0) :
    cmp99SourceFlatFullComplexPrecisionStabilizedQprimeStarFieldCLM
        (d := d) (M := M) (N' := N') (Nc := Nc) mass a =
      G.comp (cmp99SourceFlatFullComplexWeightedAdjointCLM
        (d := d) (M := M) (N' := N') (Nc := Nc)) := by
  let K := cmp99SourceFlatFullComplexPrecisionCLM
    (d := d) (M := M) (N' := N') (Nc := Nc) mass a
  let H :=
    cmp99SourceFlatFullComplexPrecisionStabilizedQprimeStarFieldCLM
      (d := d) (M := M) (N' := N') (Nc := Nc) mass a
  let Qstar := cmp99SourceFlatFullComplexWeightedAdjointCLM
    (d := d) (M := M) (N' := N') (Nc := Nc)
  have hKH : K.comp H = Qstar :=
    cmp99SourceFlatFullComplexPrecisionCLM_comp_stabilizedFieldCLM
      (d := d) (M := M) (N' := N') (Nc := Nc)
      mass a hfine hstabilized
  calc
    H = (ContinuousLinearMap.id ℂ _).comp H := by simp
    _ = (G.comp K).comp H := by rw [hGK]
    _ = G.comp (K.comp H) := ContinuousLinearMap.comp_assoc _ _ _
    _ = G.comp Qstar := by rw [hKH]

end

end YangMills.RG
