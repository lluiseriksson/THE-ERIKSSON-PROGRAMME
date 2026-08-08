/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116Eq220ComplexPotential
import YangMills.RG.BalabanCMP116SourcePhysicalCoordinateDictionary
import YangMills.RG.BalabanCMP116Eq214PhysicalContourDensity

/-!
# The literal CMP116 potential on physical source coordinates

In the source-specific contour the Gaussian coordinate is already indexed by
a physical bond and one Lie coordinate.  This module therefore installs the
literal potential of equations (1.42), (2.14), and (2.20) without passing
through an unrelated cube-coordinate representation.

The localized physical energy is proved equal to the scalar energy on the
canonical source carrier.  No coordinate comparison constant is introduced.
-/

namespace YangMills.RG

open Matrix
open scoped BigOperators RealInnerProductSpace

noncomputable section

private abbrev PhysicalEndomorphism (d N Nc : ℕ) [NeZero N] :=
  PhysicalGaugeOneCochain d N Nc →L[ℝ]
    PhysicalGaugeOneCochain d N Nc

/-- Interpret a physical-bond Gaussian coordinate as the corresponding
`su(Nc)`-valued physical one-cochain. -/
noncomputable def cmp116SourcePhysicalCoordinateCochain
    {d N Nc : ℕ} [NeZero N]
    (b : CMP116Eq214GaussianCoordinate (PhysicalBond d N) (Nc ^ 2 - 1)) :
    PhysicalGaugeOneCochain d N Nc :=
  WithLp.toLp 2 fun bond =>
    PhysicalGaugeCMP116Dictionary.sunLieCoordOfScalars fun a => b (bond, a)

@[simp] theorem cmp116SourcePhysicalCoordinateCochain_apply
    {d N Nc : ℕ} [NeZero N]
    (b : CMP116Eq214GaussianCoordinate (PhysicalBond d N) (Nc ^ 2 - 1))
    (bond : PhysicalBond d N) :
    cmp116SourcePhysicalCoordinateCochain b bond =
      PhysicalGaugeCMP116Dictionary.sunLieCoordOfScalars
        (fun a => b (bond, a)) := by
  rfl

/-- Exact source-coordinate form of the localized physical energy. -/
theorem sum_norm_sq_cmp116SourcePhysicalCoordinateCochain
    {d M N' Nc L lieDim : ℕ}
    [NeZero d] [NeZero M] [NeZero N'] [NeZero (M * N')]
    [NeZero Nc] [NeZero L] [NeZero lieDim]
    (Dict : PhysicalGaugeCMP116Dictionary d (M * N') Nc d L lieDim)
    (Z0 : Finset (FinBox d N'))
    (b : CMP116Eq214GaussianCoordinate
      (PhysicalBond d (M * N')) (Nc ^ 2 - 1)) :
    (∑ bond ∈
        PhysicalGaugeCMP116Dictionary.cmp116Eq223PhysicalInteriorBonds Z0,
        ‖cmp116SourcePhysicalCoordinateCochain b bond‖ ^ 2) =
      ∑ ba ∈ cmp116SourcePhysicalLocalizedCoordinates Dict Z0, b ba ^ 2 := by
  classical
  have hbond :
      ∀ bond : PhysicalBond d (M * N'),
        ‖cmp116SourcePhysicalCoordinateCochain b bond‖ ^ 2 =
          ∑ a : Fin (Nc ^ 2 - 1), b (bond, a) ^ 2 := by
    intro bond
    rw [EuclideanSpace.real_norm_sq_eq]
    simp [cmp116SourcePhysicalCoordinateCochain,
      PhysicalGaugeCMP116Dictionary.sunLieCoordOfScalars]
  rw [Finset.sum_congr rfl fun bond _ => hbond bond]
  simp only [
    PhysicalGaugeCMP116Dictionary.cmp116Eq223PhysicalInteriorBonds,
    Finset.sum_filter]
  have hdistribute :
      (∑ bond : PhysicalBond d (M * N'),
          if cmp116BondInterior Z0 bond then
            ∑ a : Fin (Nc ^ 2 - 1), b (bond, a) ^ 2
          else 0) =
        ∑ bond : PhysicalBond d (M * N'),
          ∑ a : Fin (Nc ^ 2 - 1),
            if cmp116BondInterior Z0 bond then b (bond, a) ^ 2 else 0 := by
    apply Finset.sum_congr rfl
    intro bond _
    by_cases hbond : cmp116BondInterior Z0 bond <;> simp [hbond]
  rw [hdistribute]
  calc
    (∑ bond : PhysicalBond d (M * N'),
        ∑ a : Fin (Nc ^ 2 - 1),
          if cmp116BondInterior Z0 bond then b (bond, a) ^ 2 else 0) =
        ∑ ba : PhysicalGaugeCoordIndex d (M * N') Nc,
          if cmp116BondInterior Z0 ba.1 then b ba ^ 2 else 0 := by
            simp only [Fintype.sum_prod_type]
    _ = ∑ ba ∈ cmp116SourcePhysicalLocalizedCoordinates Dict Z0,
        b ba ^ 2 := by
          have hfilter :
              Finset.univ.filter
                  (fun ba : PhysicalGaugeCoordIndex d (M * N') Nc =>
                    cmp116BondInterior Z0 ba.1) =
                cmp116SourcePhysicalLocalizedCoordinates Dict Z0 := by
            ext ba
            simp [mem_cmp116SourcePhysicalLocalizedCoordinates_iff]
          rw [← hfilter]
          exact (Finset.sum_filter _ _).symm

/-- The literal complex potential evaluated on the physical source Gaussian
coordinate localized to `Z0`. -/
noncomputable def cmp116SourcePhysicalComplexTauPotentialCoordinate
    {Y : Type*} [DecidableEq Y]
    {d M N' Nc L lieDim : ℕ}
    [NeZero d] [NeZero M] [NeZero N'] [NeZero (M * N')]
    [NeZero Nc] [NeZero L] [NeZero lieDim]
    (_Dict : PhysicalGaugeCMP116Dictionary d (M * N') Nc d L lieDim)
    (D : Finset Y) (tau : Y → ℂ)
    (quadratic : Y → PhysicalGaugeOneCochain d (M * N') Nc →
      PhysicalEndomorphism d (M * N') Nc)
    (remainder : Y → PhysicalGaugeOneCochain d (M * N') Nc → ℝ)
    (Z0 : Finset (FinBox d N'))
    (b : CMP116Eq214GaussianCoordinate
      (PhysicalBond d (M * N')) (Nc ^ 2 - 1)) : ℂ :=
  let S :=
    PhysicalGaugeCMP116Dictionary.cmp116Eq223PhysicalInteriorBonds
      (d := d) (M := M) (N' := N') Z0
  let B := physicalBondProjection S
    (cmp116SourcePhysicalCoordinateCochain b)
  cmp116Eq214PhysicalComplexTauPotential D tau quadratic remainder B

@[simp] theorem cmp116SourcePhysicalComplexTauPotentialCoordinate_zero
    {Y : Type*} [DecidableEq Y]
    {d M N' Nc L lieDim : ℕ}
    [NeZero d] [NeZero M] [NeZero N'] [NeZero (M * N')]
    [NeZero Nc] [NeZero L] [NeZero lieDim]
    (Dict : PhysicalGaugeCMP116Dictionary d (M * N') Nc d L lieDim)
    (D : Finset Y)
    (quadratic : Y → PhysicalGaugeOneCochain d (M * N') Nc →
      PhysicalEndomorphism d (M * N') Nc)
    (remainder : Y → PhysicalGaugeOneCochain d (M * N') Nc → ℝ)
    (Z0 : Finset (FinBox d N'))
    (b : CMP116Eq214GaussianCoordinate
      (PhysicalBond d (M * N')) (Nc ^ 2 - 1)) :
    cmp116SourcePhysicalComplexTauPotentialCoordinate
      Dict D 0 quadratic remainder Z0 b = 0 := by
  simp [cmp116SourcePhysicalComplexTauPotentialCoordinate]

/-- Equation (2.20) in the exact physical source coordinate space. -/
theorem re_cmp116SourcePhysicalComplexTauPotentialCoordinate_le_localized
    {Y : Type*} [DecidableEq Y]
    {d M N' Nc L lieDim : ℕ}
    [NeZero d] [NeZero M] [NeZero N'] [NeZero (M * N')]
    [NeZero Nc] [NeZero L] [NeZero lieDim]
    (Dict : PhysicalGaugeCMP116Dictionary d (M * N') Nc d L lieDim)
    (D : Finset Y) (tau : Y → ℂ)
    (quadratic : Y → PhysicalGaugeOneCochain d (M * N') Nc →
      PhysicalEndomorphism d (M * N') Nc)
    (remainder : Y → PhysicalGaugeOneCochain d (M * N') Nc → ℝ)
    (amplitude residualWeight : Y → ℝ)
    {kappa rowSum : ℝ}
    (hrowSum : 0 ≤ rowSum)
    (hrow : ∀ target : PhysicalBond d (M * N'),
      ∑ source : PhysicalBond d (M * N'),
        Real.exp (-(kappa * (physicalBondDist target source : ℝ))) ≤ rowSum)
    (Z0 : Finset (FinBox d N'))
    (b : CMP116Eq214GaussianCoordinate
      (PhysicalBond d (M * N')) (Nc ^ 2 - 1))
    (hquadratic : ∀ y ∈ D,
      PhysicalCovarianceExponentialKernelBound
        (quadratic y
          (physicalBondProjection
            (PhysicalGaugeCMP116Dictionary.cmp116Eq223PhysicalInteriorBonds Z0)
            (cmp116SourcePhysicalCoordinateCochain b)))
        physicalBondDist (amplitude y) kappa)
    (hremainder : ∀ y ∈ D,
      ‖tau y‖ *
          |remainder y
            (physicalBondProjection
              (PhysicalGaugeCMP116Dictionary.cmp116Eq223PhysicalInteriorBonds Z0)
              (cmp116SourcePhysicalCoordinateCochain b))| ≤
        residualWeight y) :
    (cmp116SourcePhysicalComplexTauPotentialCoordinate
        Dict D tau quadratic remainder Z0 b).re ≤
      (∑ y ∈ D, ‖tau y‖ * amplitude y * rowSum) / 2 *
          (∑ ba ∈ cmp116SourcePhysicalLocalizedCoordinates Dict Z0,
            b ba ^ 2) +
        ∑ y ∈ D, residualWeight y := by
  let S :=
    PhysicalGaugeCMP116Dictionary.cmp116Eq223PhysicalInteriorBonds
      (d := d) (M := M) (N' := N') Z0
  let B := physicalBondProjection S
    (cmp116SourcePhysicalCoordinateCochain b)
  have hsupport : ∀ bond, bond ∉ S → B bond = 0 := by
    intro bond hbond
    exact physicalBondProjection_apply_not_mem S hbond _
  have hphysical :=
    cmp116Eq220_re_physicalComplexTauPotential_le_localized
      D S tau quadratic remainder amplitude residualWeight
      hrowSum hrow B hsupport hquadratic hremainder
  have henergy :
      (∑ bond ∈ S, ‖B bond‖ ^ 2) =
        ∑ ba ∈ cmp116SourcePhysicalLocalizedCoordinates Dict Z0,
          b ba ^ 2 := by
    calc
      (∑ bond ∈ S, ‖B bond‖ ^ 2) =
          ∑ bond ∈ S,
            ‖cmp116SourcePhysicalCoordinateCochain b bond‖ ^ 2 := by
              apply Finset.sum_congr rfl
              intro bond hbond
              rw [physicalBondProjection_apply_mem S hbond]
      _ = ∑ ba ∈ cmp116SourcePhysicalLocalizedCoordinates Dict Z0,
          b ba ^ 2 := by
            simpa [S] using
              sum_norm_sq_cmp116SourcePhysicalCoordinateCochain Dict Z0 b
  simpa [cmp116SourcePhysicalComplexTauPotentialCoordinate, S, B, henergy]
    using hphysical

namespace CMP116Eq214PhysicalContourDensity

/-- Install the literal physical source potential without changing the
Gaussian or operator data of the contour density. -/
def withSourcePhysicalComplexTauPotential
    {nDelta nY d M N' Nc L lieDim : ℕ}
    {Site E : Type*} {Psi Phi : Site → Type*}
    [NeZero d] [NeZero M] [NeZero N'] [NeZero (M * N')]
    [NeZero Nc] [NeZero L] [NeZero lieDim] [Norm E]
    (C : CMP116Eq214PhysicalContourDensity nDelta nY
      (PhysicalBond d (M * N')) Site Psi Phi E (Nc ^ 2 - 1))
    (Dict : PhysicalGaugeCMP116Dictionary d (M * N') Nc d L lieDim)
    (D : Finset (Fin nY))
    (quadratic :
      (Fin nDelta → ℂ) →
      RestrictedField C.spectatorSupport Psi →
      RestrictedField C.fluctuationSupport Phi →
      Fin nY → PhysicalGaugeOneCochain d (M * N') Nc →
        PhysicalEndomorphism d (M * N') Nc)
    (remainder :
      (Fin nDelta → ℂ) →
      RestrictedField C.spectatorSupport Psi →
      RestrictedField C.fluctuationSupport Phi →
      Fin nY → PhysicalGaugeOneCochain d (M * N') Nc → ℝ)
    (Z0 : Finset (FinBox d N')) :
    CMP116Eq214PhysicalContourDensity nDelta nY
      (PhysicalBond d (M * N')) Site Psi Phi E (Nc ^ 2 - 1) where
  spectatorSupport := C.spectatorSupport
  fluctuationSupport := C.fluctuationSupport
  deltaRadius := C.deltaRadius
  yRadius := C.yRadius
  referenceRoot := C.referenceRoot
  baseGamma := C.baseGamma
  contourGamma := C.contourGamma
  baseCovariance := C.baseCovariance
  contourCovariance := C.contourCovariance
  basePrecision := C.basePrecision
  contourPrecision := C.contourPrecision
  determinantDensity := C.determinantDensity
  potential := fun sigma tau psi phi b =>
    cmp116SourcePhysicalComplexTauPotentialCoordinate
      Dict D tau (quadratic sigma psi phi) (remainder sigma psi phi) Z0 b
  bondField := C.bondField
  threshold := C.threshold
  contourGamma_zero := C.contourGamma_zero
  contourCovariance_zero := C.contourCovariance_zero
  contourPrecision_zero := C.contourPrecision_zero
  determinantDensity_zero := C.determinantDensity_zero
  determinantDensity_sq_mul_basePrecision_det :=
    C.determinantDensity_sq_mul_basePrecision_det
  potential_zero := by
    intro psi phi b
    exact cmp116SourcePhysicalComplexTauPotentialCoordinate_zero
      Dict D (quadratic 0 psi phi) (remainder 0 psi phi) Z0 b

@[simp] theorem withSourcePhysicalComplexTauPotential_potential
    {nDelta nY d M N' Nc L lieDim : ℕ}
    {Site E : Type*} {Psi Phi : Site → Type*}
    [NeZero d] [NeZero M] [NeZero N'] [NeZero (M * N')]
    [NeZero Nc] [NeZero L] [NeZero lieDim] [Norm E]
    (C : CMP116Eq214PhysicalContourDensity nDelta nY
      (PhysicalBond d (M * N')) Site Psi Phi E (Nc ^ 2 - 1))
    (Dict : PhysicalGaugeCMP116Dictionary d (M * N') Nc d L lieDim)
    (D : Finset (Fin nY))
    (quadratic :
      (Fin nDelta → ℂ) →
      RestrictedField C.spectatorSupport Psi →
      RestrictedField C.fluctuationSupport Phi →
      Fin nY → PhysicalGaugeOneCochain d (M * N') Nc →
        PhysicalEndomorphism d (M * N') Nc)
    (remainder :
      (Fin nDelta → ℂ) →
      RestrictedField C.spectatorSupport Psi →
      RestrictedField C.fluctuationSupport Phi →
      Fin nY → PhysicalGaugeOneCochain d (M * N') Nc → ℝ)
    (Z0 : Finset (FinBox d N'))
    (sigma : Fin nDelta → ℂ) (tau : Fin nY → ℂ)
    (psi : RestrictedField C.spectatorSupport Psi)
    (phi : RestrictedField C.fluctuationSupport Phi)
    (b : CMP116Eq214GaussianCoordinate
      (PhysicalBond d (M * N')) (Nc ^ 2 - 1)) :
    (C.withSourcePhysicalComplexTauPotential
      Dict D quadratic remainder Z0).potential sigma tau psi phi b =
      cmp116SourcePhysicalComplexTauPotentialCoordinate
        Dict D tau (quadratic sigma psi phi)
          (remainder sigma psi phi) Z0 b := by
  rfl

/-- Source-coordinate equation (2.20) for the potential installed in the
contour density. -/
theorem re_withSourcePhysicalComplexTauPotential_potential_le_localized
    {nDelta nY d M N' Nc L lieDim : ℕ}
    {Site E : Type*} {Psi Phi : Site → Type*}
    [NeZero d] [NeZero M] [NeZero N'] [NeZero (M * N')]
    [NeZero Nc] [NeZero L] [NeZero lieDim] [Norm E]
    (C : CMP116Eq214PhysicalContourDensity nDelta nY
      (PhysicalBond d (M * N')) Site Psi Phi E (Nc ^ 2 - 1))
    (Dict : PhysicalGaugeCMP116Dictionary d (M * N') Nc d L lieDim)
    (D : Finset (Fin nY))
    (quadratic :
      (Fin nDelta → ℂ) →
      RestrictedField C.spectatorSupport Psi →
      RestrictedField C.fluctuationSupport Phi →
      Fin nY → PhysicalGaugeOneCochain d (M * N') Nc →
        PhysicalEndomorphism d (M * N') Nc)
    (remainder :
      (Fin nDelta → ℂ) →
      RestrictedField C.spectatorSupport Psi →
      RestrictedField C.fluctuationSupport Phi →
      Fin nY → PhysicalGaugeOneCochain d (M * N') Nc → ℝ)
    (amplitude residualWeight : Fin nY → ℝ)
    {kappa rowSum : ℝ}
    (hrowSum : 0 ≤ rowSum)
    (hrow : ∀ target : PhysicalBond d (M * N'),
      ∑ source : PhysicalBond d (M * N'),
        Real.exp (-(kappa * (physicalBondDist target source : ℝ))) ≤ rowSum)
    (Z0 : Finset (FinBox d N'))
    (sigma : Fin nDelta → ℂ) (tau : Fin nY → ℂ)
    (psi : RestrictedField C.spectatorSupport Psi)
    (phi : RestrictedField C.fluctuationSupport Phi)
    (b : CMP116Eq214GaussianCoordinate
      (PhysicalBond d (M * N')) (Nc ^ 2 - 1))
    (hquadratic : ∀ y ∈ D,
      PhysicalCovarianceExponentialKernelBound
        (quadratic sigma psi phi y
          (physicalBondProjection
            (PhysicalGaugeCMP116Dictionary.cmp116Eq223PhysicalInteriorBonds Z0)
            (cmp116SourcePhysicalCoordinateCochain b)))
        physicalBondDist (amplitude y) kappa)
    (hremainder : ∀ y ∈ D,
      ‖tau y‖ *
          |remainder sigma psi phi y
            (physicalBondProjection
              (PhysicalGaugeCMP116Dictionary.cmp116Eq223PhysicalInteriorBonds Z0)
              (cmp116SourcePhysicalCoordinateCochain b))| ≤
        residualWeight y) :
    ((C.withSourcePhysicalComplexTauPotential
        Dict D quadratic remainder Z0).potential sigma tau psi phi b).re ≤
      (∑ y ∈ D, ‖tau y‖ * amplitude y * rowSum) / 2 *
          (∑ ba ∈ cmp116SourcePhysicalLocalizedCoordinates Dict Z0,
            b ba ^ 2) +
        ∑ y ∈ D, residualWeight y := by
  exact re_cmp116SourcePhysicalComplexTauPotentialCoordinate_le_localized
    Dict D tau (quadratic sigma psi phi) (remainder sigma psi phi)
    amplitude residualWeight hrowSum hrow Z0 b hquadratic hremainder

@[simp] theorem withSourcePhysicalComplexTauPotential_r1Matrix
    {nDelta nY d M N' Nc L lieDim : ℕ}
    {Site E : Type*} {Psi Phi : Site → Type*}
    [NeZero d] [NeZero M] [NeZero N'] [NeZero (M * N')]
    [NeZero Nc] [NeZero L] [NeZero lieDim] [Norm E]
    (C : CMP116Eq214PhysicalContourDensity nDelta nY
      (PhysicalBond d (M * N')) Site Psi Phi E (Nc ^ 2 - 1))
    (Dict : PhysicalGaugeCMP116Dictionary d (M * N') Nc d L lieDim)
    (D : Finset (Fin nY))
    (quadratic :
      (Fin nDelta → ℂ) →
      RestrictedField C.spectatorSupport Psi →
      RestrictedField C.fluctuationSupport Phi →
      Fin nY → PhysicalGaugeOneCochain d (M * N') Nc →
        PhysicalEndomorphism d (M * N') Nc)
    (remainder :
      (Fin nDelta → ℂ) →
      RestrictedField C.spectatorSupport Psi →
      RestrictedField C.fluctuationSupport Phi →
      Fin nY → PhysicalGaugeOneCochain d (M * N') Nc → ℝ)
    (Z0 : Finset (FinBox d N'))
    (sigma : Fin nDelta → ℂ) (tau : Fin nY → ℂ)
    (psi : RestrictedField C.spectatorSupport Psi)
    (phi : RestrictedField C.fluctuationSupport Phi) :
    (C.withSourcePhysicalComplexTauPotential
      Dict D quadratic remainder Z0).r1Matrix sigma tau psi phi =
      C.r1Matrix sigma tau psi phi := by
  rfl

@[simp] theorem withSourcePhysicalComplexTauPotential_r2Matrix
    {nDelta nY d M N' Nc L lieDim : ℕ}
    {Site E : Type*} {Psi Phi : Site → Type*}
    [NeZero d] [NeZero M] [NeZero N'] [NeZero (M * N')]
    [NeZero Nc] [NeZero L] [NeZero lieDim] [Norm E]
    (C : CMP116Eq214PhysicalContourDensity nDelta nY
      (PhysicalBond d (M * N')) Site Psi Phi E (Nc ^ 2 - 1))
    (Dict : PhysicalGaugeCMP116Dictionary d (M * N') Nc d L lieDim)
    (D : Finset (Fin nY))
    (quadratic :
      (Fin nDelta → ℂ) →
      RestrictedField C.spectatorSupport Psi →
      RestrictedField C.fluctuationSupport Phi →
      Fin nY → PhysicalGaugeOneCochain d (M * N') Nc →
        PhysicalEndomorphism d (M * N') Nc)
    (remainder :
      (Fin nDelta → ℂ) →
      RestrictedField C.spectatorSupport Psi →
      RestrictedField C.fluctuationSupport Phi →
      Fin nY → PhysicalGaugeOneCochain d (M * N') Nc → ℝ)
    (Z0 : Finset (FinBox d N'))
    (sigma : Fin nDelta → ℂ) (tau : Fin nY → ℂ)
    (psi : RestrictedField C.spectatorSupport Psi)
    (phi : RestrictedField C.fluctuationSupport Phi) :
    (C.withSourcePhysicalComplexTauPotential
      Dict D quadratic remainder Z0).r2Matrix sigma tau psi phi =
      C.r2Matrix sigma tau psi phi := by
  rfl

@[simp] theorem withSourcePhysicalComplexTauPotential_r3Matrix
    {nDelta nY d M N' Nc L lieDim : ℕ}
    {Site E : Type*} {Psi Phi : Site → Type*}
    [NeZero d] [NeZero M] [NeZero N'] [NeZero (M * N')]
    [NeZero Nc] [NeZero L] [NeZero lieDim] [Norm E]
    (C : CMP116Eq214PhysicalContourDensity nDelta nY
      (PhysicalBond d (M * N')) Site Psi Phi E (Nc ^ 2 - 1))
    (Dict : PhysicalGaugeCMP116Dictionary d (M * N') Nc d L lieDim)
    (D : Finset (Fin nY))
    (quadratic :
      (Fin nDelta → ℂ) →
      RestrictedField C.spectatorSupport Psi →
      RestrictedField C.fluctuationSupport Phi →
      Fin nY → PhysicalGaugeOneCochain d (M * N') Nc →
        PhysicalEndomorphism d (M * N') Nc)
    (remainder :
      (Fin nDelta → ℂ) →
      RestrictedField C.spectatorSupport Psi →
      RestrictedField C.fluctuationSupport Phi →
      Fin nY → PhysicalGaugeOneCochain d (M * N') Nc → ℝ)
    (Z0 : Finset (FinBox d N'))
    (sigma : Fin nDelta → ℂ) (tau : Fin nY → ℂ)
    (psi : RestrictedField C.spectatorSupport Psi)
    (phi : RestrictedField C.fluctuationSupport Phi) :
    (C.withSourcePhysicalComplexTauPotential
      Dict D quadratic remainder Z0).r3Matrix sigma tau psi phi =
      C.r3Matrix sigma tau psi phi := by
  rfl

end CMP116Eq214PhysicalContourDensity

end

end YangMills.RG
