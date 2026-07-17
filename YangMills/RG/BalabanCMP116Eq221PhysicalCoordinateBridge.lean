/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116Eq221PhysicalClosure
import YangMills.RG.BalabanCMP116Eq223PhysicalLocalizationProjector
import YangMills.RG.BalabanCMP116Eq222CutoffSuppression

/-!
# Coordinate bridge for the physical CMP116 equation-(2.21) bound

The physical kernel argument is performed on `su(Nc)`-valued bond blocks,
whereas the Gaussian domination layer uses flattened scalar coordinates.
This module proves that localization commutes with the exact physical/CMP116
isometry.  In particular, the physical localized energy is literally the
quadratic form of the canonical scalar projector `P_Z0`; no comparison
constant or Lie-coordinate multiplicity is introduced.
-/

namespace YangMills.RG

open Matrix
open scoped BigOperators RealInnerProductSpace

noncomputable section

namespace PhysicalGaugeCMP116Dictionary

variable {d M N' Nc L lieDim : ℕ}
variable [NeZero d] [NeZero M] [NeZero N'] [NeZero (M * N')]
variable [NeZero Nc] [NeZero L] [NeZero lieDim]

/-- Exact localized-energy identity under the physical/CMP116 coordinate
isometry. -/
theorem sum_norm_sq_flatPhysicalLinearIsometryEquiv_physicalInteriorBonds
    (Dict : PhysicalGaugeCMP116Dictionary d (M * N') Nc d L lieDim)
    (Z0 : Finset (FinBox d N'))
    (x : EuclideanSpace ℝ (CMP116CoordIndex d L lieDim)) :
    (∑ b ∈ cmp116Eq223PhysicalInteriorBonds
          (d := d) (M := M) (N' := N') Z0,
        ‖Dict.flatPhysicalLinearIsometryEquiv x b‖ ^ 2) =
      ∑ qa ∈ Dict.cmp116Eq223PhysicalLocalizedCoordinates Z0, x qa ^ 2 := by
  classical
  have hbond :
      ∀ b : PhysicalBond d (M * N'),
        ‖Dict.flatPhysicalLinearIsometryEquiv x b‖ ^ 2 =
          ∑ a : Fin (Nc ^ 2 - 1),
            x (Dict.coordEquiv.symm (b, a)) ^ 2 := by
    intro b
    change
      ‖Dict.pullFluctuationCochain (fun q a => x (q, a)) b‖ ^ 2 =
        ∑ a : Fin (Nc ^ 2 - 1),
          x (Dict.coordEquiv.symm (b, a)) ^ 2
    rw [EuclideanSpace.real_norm_sq_eq]
    simp [pullFluctuationCochain, sunLieCoordOfScalars]
  rw [Finset.sum_congr rfl fun b _ => hbond b]
  simp only [cmp116Eq223PhysicalInteriorBonds,
    cmp116Eq223PhysicalLocalizedCoordinates, Finset.sum_filter]
  have hdistribute :
      (∑ b : PhysicalBond d (M * N'),
          if cmp116BondInterior Z0 b then
            ∑ a : Fin (Nc ^ 2 - 1),
              x (Dict.coordEquiv.symm (b, a)) ^ 2
          else 0) =
        ∑ b : PhysicalBond d (M * N'),
          ∑ a : Fin (Nc ^ 2 - 1),
            if cmp116BondInterior Z0 b then
              x (Dict.coordEquiv.symm (b, a)) ^ 2
            else 0 := by
    apply Finset.sum_congr rfl
    intro b _
    by_cases hb : cmp116BondInterior Z0 b <;> simp [hb]
  rw [hdistribute]
  have hreindex :=
    Equiv.sum_comp Dict.coordEquiv.symm
      (fun qa : CMP116CoordIndex d L lieDim =>
        if cmp116BondInterior Z0 (Dict.coordEquiv qa).1
        then x qa ^ 2 else 0)
  simpa only [Dict.coordEquiv.apply_symm_apply, Prod.fst,
    Fintype.sum_prod_type] using hreindex

/-- The physical localized energy is exactly the quadratic form of the
canonical flattened projector `P_Z0`. -/
theorem sum_norm_sq_flatPhysicalLinearIsometryEquiv_physicalInteriorBonds_eq_dotProduct
    (Dict : PhysicalGaugeCMP116Dictionary d (M * N') Nc d L lieDim)
    (Z0 : Finset (FinBox d N'))
    (x : EuclideanSpace ℝ (CMP116CoordIndex d L lieDim)) :
    (∑ b ∈ cmp116Eq223PhysicalInteriorBonds
          (d := d) (M := M) (N' := N') Z0,
        ‖Dict.flatPhysicalLinearIsometryEquiv x b‖ ^ 2) =
      x ⬝ᵥ
        (cmp116Eq223CoordinateProjection
          (Dict.cmp116Eq223PhysicalLocalizedCoordinates Z0) *ᵥ x) := by
  rw [Dict.dotProduct_physicalLocalizationProjection_mulVec]
  exact
    Dict.sum_norm_sq_flatPhysicalLinearIsometryEquiv_physicalInteriorBonds
      Z0 x

end PhysicalGaugeCMP116Dictionary

private abbrev PhysicalEndomorphism (d N Nc : ℕ) [NeZero N] :=
  PhysicalGaugeOneCochain d N Nc →L[ℝ]
    PhysicalGaugeOneCochain d N Nc

/-- Coordinate-facing equation-(2.21) estimate.  Both fluctuation fields are
localized by the physical projector, while the right-hand side is written
literally as the scalar quadratic form of `P_Z0`. -/
theorem CMP116Eq216PhysicalKernelCertificate.three_operator_forms_le_coordinateLocalization_geometric
    {d M N' Nc L lieDim : ℕ}
    [NeZero d] [NeZero M] [NeZero N'] [NeZero (M * N')]
    [NeZero Nc] [NeZero L] [NeZero lieDim]
    (Dict : PhysicalGaugeCMP116Dictionary d (M * N') Nc d L lieDim)
    (Z0 : Finset (FinBox d N'))
    {R₁ R₂ R₃ : PhysicalEndomorphism d (M * N') Nc}
    (cert : CMP116Eq216PhysicalKernelCertificate
      R₁ R₂ R₃ physicalBondDist)
    (hgeom :
      ((2 ^ d : ℕ) : ℝ) * Real.exp (-cert.rate) < 1)
    (x b : EuclideanSpace ℝ (CMP116CoordIndex d L lieDim)) :
    let S : Finset (PhysicalBond d (M * N')) :=
      PhysicalGaugeCMP116Dictionary.cmp116Eq223PhysicalInteriorBonds Z0
    let X := physicalBondProjection S
      (Dict.flatPhysicalLinearIsometryEquiv x)
    let B := physicalBondProjection S
      (Dict.flatPhysicalLinearIsometryEquiv b)
    (1 / 2 : ℝ) * |inner ℝ X (R₁ X)| +
        (1 / 2 : ℝ) * |inner ℝ B (R₂ B)| +
        |inner ℝ B (R₃ X)| ≤
      (cert.amplitude *
          cmp116Eq221PhysicalRowSum d cert.rate) *
        (x ⬝ᵥ
            (cmp116Eq223CoordinateProjection
              (Dict.cmp116Eq223PhysicalLocalizedCoordinates Z0) *ᵥ x) +
          b ⬝ᵥ
            (cmp116Eq223CoordinateProjection
              (Dict.cmp116Eq223PhysicalLocalizedCoordinates Z0) *ᵥ b)) := by
  dsimp only
  let S : Finset (PhysicalBond d (M * N')) :=
    PhysicalGaugeCMP116Dictionary.cmp116Eq223PhysicalInteriorBonds Z0
  let X := physicalBondProjection S
    (Dict.flatPhysicalLinearIsometryEquiv x)
  let B := physicalBondProjection S
    (Dict.flatPhysicalLinearIsometryEquiv b)
  have hsupportX : ∀ i, i ∉ S → X i = 0 := by
    intro i hi
    exact physicalBondProjection_apply_not_mem S hi _
  have hsupportB : ∀ i, i ∉ S → B i = 0 := by
    intro i hi
    exact physicalBondProjection_apply_not_mem S hi _
  have henergyX :
      (∑ i ∈ S, ‖X i‖ ^ 2) =
        x ⬝ᵥ
          (cmp116Eq223CoordinateProjection
            (Dict.cmp116Eq223PhysicalLocalizedCoordinates Z0) *ᵥ x) := by
    calc
      (∑ i ∈ S, ‖X i‖ ^ 2) =
          ∑ i ∈ S, ‖Dict.flatPhysicalLinearIsometryEquiv x i‖ ^ 2 := by
        apply Finset.sum_congr rfl
        intro i hi
        have hXi : X i = Dict.flatPhysicalLinearIsometryEquiv x i := by
          dsimp [X]
          exact physicalBondProjection_apply_mem S hi _
        rw [hXi]
      _ = x ⬝ᵥ
          (cmp116Eq223CoordinateProjection
            (Dict.cmp116Eq223PhysicalLocalizedCoordinates Z0) *ᵥ x) := by
        dsimp [S]
        exact
          Dict.sum_norm_sq_flatPhysicalLinearIsometryEquiv_physicalInteriorBonds_eq_dotProduct
            Z0 x
  have henergyB :
      (∑ i ∈ S, ‖B i‖ ^ 2) =
        b ⬝ᵥ
          (cmp116Eq223CoordinateProjection
            (Dict.cmp116Eq223PhysicalLocalizedCoordinates Z0) *ᵥ b) := by
    calc
      (∑ i ∈ S, ‖B i‖ ^ 2) =
          ∑ i ∈ S, ‖Dict.flatPhysicalLinearIsometryEquiv b i‖ ^ 2 := by
        apply Finset.sum_congr rfl
        intro i hi
        have hBi : B i = Dict.flatPhysicalLinearIsometryEquiv b i := by
          dsimp [B]
          exact physicalBondProjection_apply_mem S hi _
        rw [hBi]
      _ = b ⬝ᵥ
          (cmp116Eq223CoordinateProjection
            (Dict.cmp116Eq223PhysicalLocalizedCoordinates Z0) *ᵥ b) := by
        dsimp [S]
        exact
          Dict.sum_norm_sq_flatPhysicalLinearIsometryEquiv_physicalInteriorBonds_eq_dotProduct
            Z0 b
  have hphysical :=
    cert.three_operator_forms_le_localized_geometric
      hgeom S S X B hsupportX hsupportB
  simpa only [henergyX, henergyB] using hphysical

/-- Scalar-coordinate terminal form of the physical (2.20)--(2.22)
absorption.  The equation-(2.21) premise and its coefficient are generated
from the physical kernel certificate; the conclusion is already written with
the exact Gaussian projector `P_Z0`. -/
theorem CMP116Eq216PhysicalKernelCertificate.three_operator_forms_absorb_into_coordinateAlpha5_geometric
    {d M N' Nc L lieDim : ℕ}
    [NeZero d] [NeZero M] [NeZero N'] [NeZero (M * N')]
    [NeZero Nc] [NeZero L] [NeZero lieDim]
    (Dict : PhysicalGaugeCMP116Dictionary d (M * N') Nc d L lieDim)
    (Z0 : Finset (FinBox d N'))
    {R₁ R₂ R₃ : PhysicalEndomorphism d (M * N') Nc}
    (cert : CMP116Eq216PhysicalKernelCertificate
      R₁ R₂ R₃ physicalBondDist)
    (hgeom :
      ((2 ^ d : ℕ) : ℝ) * Real.exp (-cert.rate) < 1)
    (x b : EuclideanSpace ℝ (CMP116CoordIndex d L lieDim))
    {potentialTerm potentialRate cutoff alpha5 energyP residual20 : ℝ}
    (hpotential :
      potentialTerm ≤
        potentialRate / 2 *
          (b ⬝ᵥ
            (cmp116Eq223CoordinateProjection
              (Dict.cmp116Eq223PhysicalLocalizedCoordinates Z0) *ᵥ b)) +
          residual20)
    (henergy :
      energyP ≤
        b ⬝ᵥ
          (cmp116Eq223CoordinateProjection
            (Dict.cmp116Eq223PhysicalLocalizedCoordinates Z0) *ᵥ b))
    (hpotentialRate : 0 ≤ potentialRate)
    (hcutoff : 0 ≤ cutoff)
    (hbudget :
      potentialRate +
          2 * (cert.amplitude *
            cmp116Eq221PhysicalRowSum d cert.rate) +
          cutoff ≤ alpha5) :
    let S : Finset (PhysicalBond d (M * N')) :=
      PhysicalGaugeCMP116Dictionary.cmp116Eq223PhysicalInteriorBonds Z0
    let X := physicalBondProjection S
      (Dict.flatPhysicalLinearIsometryEquiv x)
    let B := physicalBondProjection S
      (Dict.flatPhysicalLinearIsometryEquiv b)
    potentialTerm +
          ((1 / 2 : ℝ) * |inner ℝ X (R₁ X)| +
            (1 / 2 : ℝ) * |inner ℝ B (R₂ B)| +
            |inner ℝ B (R₃ X)|) +
          cutoff / 2 * energyP ≤
      alpha5 / 2 *
          (x ⬝ᵥ
              (cmp116Eq223CoordinateProjection
                (Dict.cmp116Eq223PhysicalLocalizedCoordinates Z0) *ᵥ x) +
            b ⬝ᵥ
              (cmp116Eq223CoordinateProjection
                (Dict.cmp116Eq223PhysicalLocalizedCoordinates Z0) *ᵥ b)) +
        residual20 := by
  dsimp only
  let S : Finset (PhysicalBond d (M * N')) :=
    PhysicalGaugeCMP116Dictionary.cmp116Eq223PhysicalInteriorBonds Z0
  let X := physicalBondProjection S
    (Dict.flatPhysicalLinearIsometryEquiv x)
  let B := physicalBondProjection S
    (Dict.flatPhysicalLinearIsometryEquiv b)
  let energyX : ℝ :=
    x ⬝ᵥ
      (cmp116Eq223CoordinateProjection
        (Dict.cmp116Eq223PhysicalLocalizedCoordinates Z0) *ᵥ x)
  let energyB : ℝ :=
    b ⬝ᵥ
      (cmp116Eq223CoordinateProjection
        (Dict.cmp116Eq223PhysicalLocalizedCoordinates Z0) *ᵥ b)
  let operatorTerm : ℝ :=
    (1 / 2 : ℝ) * |inner ℝ X (R₁ X)| +
      (1 / 2 : ℝ) * |inner ℝ B (R₂ B)| +
      |inner ℝ B (R₃ X)|
  let operatorRate : ℝ :=
    2 * (cert.amplitude *
      cmp116Eq221PhysicalRowSum d cert.rate)
  have hoperatorRaw :=
    cert.three_operator_forms_le_coordinateLocalization_geometric
      Dict Z0 hgeom x b
  have hoperator :
      operatorTerm ≤ operatorRate / 2 * (energyX + energyB) := by
    dsimp [operatorTerm, operatorRate, energyX, energyB, S, X, B]
    nlinarith
  have henergyX : 0 ≤ energyX := by
    dsimp [energyX]
    rw [Dict.dotProduct_physicalLocalizationProjection_mulVec]
    positivity
  have henergyB : 0 ≤ energyB := by
    dsimp [energyB]
    rw [Dict.dotProduct_physicalLocalizationProjection_mulVec]
    positivity
  have hresult := cmp116Eq220_eq221_eq222_absorb_into_alpha5
    (potentialTerm := potentialTerm)
    (operatorTerm := operatorTerm)
    (potentialRate := potentialRate)
    (operatorRate := operatorRate)
    (cutoff := cutoff)
    (alpha5 := alpha5)
    (energyP := energyP)
    (energyX := energyX)
    (energyB := energyB)
    (residual20 := residual20)
    (residual21 := 0)
    (by simpa [energyB] using hpotential)
    (by simpa using hoperator)
    (by simpa [energyB] using henergy)
    hpotentialRate hcutoff henergyX henergyB
    (by simpa [operatorRate] using hbudget)
  simpa [operatorTerm, energyX, energyB, S, X, B] using hresult

/-- Interaction-exponent form of the coordinate `alpha5` absorption.  A
source-facing identification of the real interaction exponent with the
literal potential and `R₁/R₂/R₃` terms is enough; no separate equation-(2.21)
bound remains in the interface. -/
theorem CMP116Eq216PhysicalKernelCertificate.interactionExponent_le_coordinateAlpha5_geometric
    {d M N' Nc L lieDim : ℕ}
    [NeZero d] [NeZero M] [NeZero N'] [NeZero (M * N')]
    [NeZero Nc] [NeZero L] [NeZero lieDim]
    (Dict : PhysicalGaugeCMP116Dictionary d (M * N') Nc d L lieDim)
    (Z0 : Finset (FinBox d N'))
    {R₁ R₂ R₃ : PhysicalEndomorphism d (M * N') Nc}
    (cert : CMP116Eq216PhysicalKernelCertificate
      R₁ R₂ R₃ physicalBondDist)
    (hgeom :
      ((2 ^ d : ℕ) : ℝ) * Real.exp (-cert.rate) < 1)
    (x b : EuclideanSpace ℝ (CMP116CoordIndex d L lieDim))
    {interactionExponent potentialTerm potentialRate cutoff alpha5 energyP
      residual20 : ℝ}
    (hshape :
      let S : Finset (PhysicalBond d (M * N')) :=
        PhysicalGaugeCMP116Dictionary.cmp116Eq223PhysicalInteriorBonds Z0
      let X := physicalBondProjection S
        (Dict.flatPhysicalLinearIsometryEquiv x)
      let B := physicalBondProjection S
        (Dict.flatPhysicalLinearIsometryEquiv b)
      interactionExponent ≤
        potentialTerm +
          ((1 / 2 : ℝ) * |inner ℝ X (R₁ X)| +
            (1 / 2 : ℝ) * |inner ℝ B (R₂ B)| +
            |inner ℝ B (R₃ X)|))
    (hpotential :
      potentialTerm ≤
        potentialRate / 2 *
          (b ⬝ᵥ
            (cmp116Eq223CoordinateProjection
              (Dict.cmp116Eq223PhysicalLocalizedCoordinates Z0) *ᵥ b)) +
          residual20)
    (henergy :
      energyP ≤
        b ⬝ᵥ
          (cmp116Eq223CoordinateProjection
            (Dict.cmp116Eq223PhysicalLocalizedCoordinates Z0) *ᵥ b))
    (hpotentialRate : 0 ≤ potentialRate)
    (hcutoff : 0 ≤ cutoff)
    (hbudget :
      potentialRate +
          2 * (cert.amplitude *
            cmp116Eq221PhysicalRowSum d cert.rate) +
          cutoff ≤ alpha5) :
    interactionExponent + cutoff / 2 * energyP ≤
      alpha5 / 2 *
          (x ⬝ᵥ
              (cmp116Eq223CoordinateProjection
                (Dict.cmp116Eq223PhysicalLocalizedCoordinates Z0) *ᵥ x) +
            b ⬝ᵥ
              (cmp116Eq223CoordinateProjection
                (Dict.cmp116Eq223PhysicalLocalizedCoordinates Z0) *ᵥ b)) +
        residual20 := by
  let S : Finset (PhysicalBond d (M * N')) :=
    PhysicalGaugeCMP116Dictionary.cmp116Eq223PhysicalInteriorBonds Z0
  let X := physicalBondProjection S
    (Dict.flatPhysicalLinearIsometryEquiv x)
  let B := physicalBondProjection S
    (Dict.flatPhysicalLinearIsometryEquiv b)
  let operatorTerm : ℝ :=
    (1 / 2 : ℝ) * |inner ℝ X (R₁ X)| +
      (1 / 2 : ℝ) * |inner ℝ B (R₂ B)| +
      |inner ℝ B (R₃ X)|
  have habsorb :=
    cert.three_operator_forms_absorb_into_coordinateAlpha5_geometric
      Dict Z0 hgeom x b hpotential henergy hpotentialRate hcutoff hbudget
  have hshape' : interactionExponent ≤ potentialTerm + operatorTerm := by
    simpa [S, X, B, operatorTerm] using hshape
  calc
    interactionExponent + cutoff / 2 * energyP ≤
        potentialTerm + operatorTerm + cutoff / 2 * energyP := by
      linarith
    _ ≤ alpha5 / 2 *
          (x ⬝ᵥ
              (cmp116Eq223CoordinateProjection
                (Dict.cmp116Eq223PhysicalLocalizedCoordinates Z0) *ᵥ x) +
            b ⬝ᵥ
              (cmp116Eq223CoordinateProjection
                (Dict.cmp116Eq223PhysicalLocalizedCoordinates Z0) *ᵥ b)) +
        residual20 := by
      simpa [S, X, B, operatorTerm] using habsorb

/-- Physical-cutoff specialization of the interaction-exponent bound.  The
selected energy in equation (2.22) is now the canonical coordinate carrier of
the physical bond set `P`, and admissibility of `(D,P,Z0)` proves its inclusion
in `P_Z0` internally.  Thus no `henergy` premise remains. -/
theorem CMP116Eq216PhysicalKernelCertificate.interactionExponent_le_coordinateAlpha5_physicalCutoff_geometric
    {d M N' Nc L lieDim : ℕ}
    [NeZero d] [NeZero M] [NeZero N'] [NeZero (M * N')]
    [NeZero Nc] [NeZero L] [NeZero lieDim]
    (Dict : PhysicalGaugeCMP116Dictionary d (M * N') Nc d L lieDim)
    (Dset : Finset (Finset (FinBox d N')))
    (P : Finset (PhysicalBond d (M * N')))
    (Z0 : Finset (FinBox d N'))
    (hZ0 : CMP116LocalizationAdmissible Dset P Z0)
    {R₁ R₂ R₃ : PhysicalEndomorphism d (M * N') Nc}
    (cert : CMP116Eq216PhysicalKernelCertificate
      R₁ R₂ R₃ physicalBondDist)
    (hgeom :
      ((2 ^ d : ℕ) : ℝ) * Real.exp (-cert.rate) < 1)
    (x b : EuclideanSpace ℝ (CMP116CoordIndex d L lieDim))
    {interactionExponent potentialTerm potentialRate cutoff alpha5 residual20 : ℝ}
    (hshape :
      let S : Finset (PhysicalBond d (M * N')) :=
        PhysicalGaugeCMP116Dictionary.cmp116Eq223PhysicalInteriorBonds Z0
      let X := physicalBondProjection S
        (Dict.flatPhysicalLinearIsometryEquiv x)
      let B := physicalBondProjection S
        (Dict.flatPhysicalLinearIsometryEquiv b)
      interactionExponent ≤
        potentialTerm +
          ((1 / 2 : ℝ) * |inner ℝ X (R₁ X)| +
            (1 / 2 : ℝ) * |inner ℝ B (R₂ B)| +
            |inner ℝ B (R₃ X)|))
    (hpotential :
      potentialTerm ≤
        potentialRate / 2 *
          (b ⬝ᵥ
            (cmp116Eq223CoordinateProjection
              (Dict.cmp116Eq223PhysicalLocalizedCoordinates Z0) *ᵥ b)) +
          residual20)
    (hpotentialRate : 0 ≤ potentialRate)
    (hcutoff : 0 ≤ cutoff)
    (hbudget :
      potentialRate +
          2 * (cert.amplitude *
            cmp116Eq221PhysicalRowSum d cert.rate) +
          cutoff ≤ alpha5) :
    interactionExponent + cutoff / 2 *
        (∑ qa ∈ Dict.cmp116Eq222SelectedCoordinates P, b qa ^ 2) ≤
      alpha5 / 2 *
          (x ⬝ᵥ
              (cmp116Eq223CoordinateProjection
                (Dict.cmp116Eq223PhysicalLocalizedCoordinates Z0) *ᵥ x) +
            b ⬝ᵥ
              (cmp116Eq223CoordinateProjection
                (Dict.cmp116Eq223PhysicalLocalizedCoordinates Z0) *ᵥ b)) +
        residual20 := by
  apply cert.interactionExponent_le_coordinateAlpha5_geometric
    Dict Z0 hgeom x b hshape hpotential
  · exact
      Dict.sum_sq_selectedCoordinates_le_dotProduct_physicalLocalizationProjection
        hZ0 b
  · exact hpotentialRate
  · exact hcutoff
  · exact hbudget

end

end YangMills.RG
