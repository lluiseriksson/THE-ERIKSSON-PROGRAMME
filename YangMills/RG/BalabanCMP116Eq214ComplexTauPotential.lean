/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116Eq220PhysicalPotential

/-!
# CMP116 equation (2.14): literal complex tau-weighted potential

The Cauchy variables `tau(Y)` multiply the real localized potentials
`V_k(Y,B)` before the Gaussian estimate.  This module constructs that complex
sum literally from the already formalized equation-(1.42) potential terms and
transports it to the finite Gaussian coordinates.

No bound on the Cauchy contour is assumed.  In particular, this is the source
producer whose real part must later be estimated by (1.36), (1.43), and (2.20),
not an arbitrary complex `potential` field.
-/

namespace YangMills.RG

open Matrix
open scoped BigOperators RealInnerProductSpace

noncomputable section

private abbrev PhysicalEndomorphism (d N Nc : ℕ) [NeZero N] :=
  PhysicalGaugeOneCochain d N Nc →L[ℝ]
    PhysicalGaugeOneCochain d N Nc

/-- The literal complex `tau`-weighted potential in equation (2.14). -/
noncomputable def cmp116Eq214PhysicalComplexTauPotential
    {Y : Type*} [DecidableEq Y]
    {d N Nc : ℕ} [NeZero N]
    (D : Finset Y) (tau : Y → ℂ)
    (quadratic : Y → PhysicalGaugeOneCochain d N Nc →
      PhysicalEndomorphism d N Nc)
    (remainder : Y → PhysicalGaugeOneCochain d N Nc → ℝ)
    (B : PhysicalGaugeOneCochain d N Nc) : ℂ :=
  ∑ y ∈ D,
    tau y * (cmp116Eq142PhysicalPotentialTerm quadratic remainder y B : ℂ)

/-- At the center of the `tau` contour the interaction potential vanishes. -/
@[simp] theorem cmp116Eq214PhysicalComplexTauPotential_zero
    {Y : Type*} [DecidableEq Y]
    {d N Nc : ℕ} [NeZero N]
    (D : Finset Y)
    (quadratic : Y → PhysicalGaugeOneCochain d N Nc →
      PhysicalEndomorphism d N Nc)
    (remainder : Y → PhysicalGaugeOneCochain d N Nc → ℝ)
    (B : PhysicalGaugeOneCochain d N Nc) :
    cmp116Eq214PhysicalComplexTauPotential D 0 quadratic remainder B = 0 := by
  simp [cmp116Eq214PhysicalComplexTauPotential]

/-- Exact real part of the complex potential.  Since each localized potential
is real, only `Re tau(Y)` contributes. -/
theorem cmp116Eq214PhysicalComplexTauPotential_re
    {Y : Type*} [DecidableEq Y]
    {d N Nc : ℕ} [NeZero N]
    (D : Finset Y) (tau : Y → ℂ)
    (quadratic : Y → PhysicalGaugeOneCochain d N Nc →
      PhysicalEndomorphism d N Nc)
    (remainder : Y → PhysicalGaugeOneCochain d N Nc → ℝ)
    (B : PhysicalGaugeOneCochain d N Nc) :
    (cmp116Eq214PhysicalComplexTauPotential
        D tau quadratic remainder B).re =
      ∑ y ∈ D, (tau y).re *
        cmp116Eq142PhysicalPotentialTerm quadratic remainder y B := by
  simp [cmp116Eq214PhysicalComplexTauPotential, Complex.mul_re]

/-- Restricting the contour parameters to the real axis recovers the existing
source-faithful real potential exactly. -/
theorem cmp116Eq214PhysicalComplexTauPotential_ofReal
    {Y : Type*} [DecidableEq Y]
    {d N Nc : ℕ} [NeZero N]
    (D : Finset Y) (tau : Y → ℝ)
    (quadratic : Y → PhysicalGaugeOneCochain d N Nc →
      PhysicalEndomorphism d N Nc)
    (remainder : Y → PhysicalGaugeOneCochain d N Nc → ℝ)
    (B : PhysicalGaugeOneCochain d N Nc) :
    cmp116Eq214PhysicalComplexTauPotential D
        (fun y => (tau y : ℂ)) quadratic remainder B =
      (cmp116Eq214PhysicalTauPotential D tau quadratic remainder B : ℂ) := by
  simp [cmp116Eq214PhysicalComplexTauPotential,
    cmp116Eq214PhysicalTauPotential]

namespace PhysicalGaugeCMP116Dictionary

/-- The same literal complex potential evaluated on the localized physical
fluctuation represented by one finite Gaussian coordinate vector. -/
noncomputable def cmp116Eq214ComplexTauPotentialCoordinate
    {Y : Type*} [DecidableEq Y]
    {d M N' Nc L lieDim : ℕ}
    [NeZero d] [NeZero M] [NeZero N'] [NeZero (M * N')]
    [NeZero Nc] [NeZero L] [NeZero lieDim]
    (Dict : PhysicalGaugeCMP116Dictionary d (M * N') Nc d L lieDim)
    (D : Finset Y) (tau : Y → ℂ)
    (quadratic : Y → PhysicalGaugeOneCochain d (M * N') Nc →
      PhysicalEndomorphism d (M * N') Nc)
    (remainder : Y → PhysicalGaugeOneCochain d (M * N') Nc → ℝ)
    (Z0 : Finset (FinBox d N'))
    (b : CMP116Eq214GaussianCoordinate (Cube d L) lieDim) : ℂ :=
  let S := cmp116Eq223PhysicalInteriorBonds Z0
  let B := physicalBondProjection S
    (Dict.flatPhysicalLinearIsometryEquiv (WithLp.toLp 2 b))
  cmp116Eq214PhysicalComplexTauPotential D tau quadratic remainder B

@[simp] theorem cmp116Eq214ComplexTauPotentialCoordinate_zero
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
    (b : CMP116Eq214GaussianCoordinate (Cube d L) lieDim) :
    Dict.cmp116Eq214ComplexTauPotentialCoordinate
        D 0 quadratic remainder Z0 b = 0 := by
  simp [cmp116Eq214ComplexTauPotentialCoordinate]

/-- Coordinate-level compatibility with the real physical potential. -/
theorem cmp116Eq214ComplexTauPotentialCoordinate_ofReal
    {Y : Type*} [DecidableEq Y]
    {d M N' Nc L lieDim : ℕ}
    [NeZero d] [NeZero M] [NeZero N'] [NeZero (M * N')]
    [NeZero Nc] [NeZero L] [NeZero lieDim]
    (Dict : PhysicalGaugeCMP116Dictionary d (M * N') Nc d L lieDim)
    (D : Finset Y) (tau : Y → ℝ)
    (quadratic : Y → PhysicalGaugeOneCochain d (M * N') Nc →
      PhysicalEndomorphism d (M * N') Nc)
    (remainder : Y → PhysicalGaugeOneCochain d (M * N') Nc → ℝ)
    (Z0 : Finset (FinBox d N'))
    (b : CMP116Eq214GaussianCoordinate (Cube d L) lieDim) :
    Dict.cmp116Eq214ComplexTauPotentialCoordinate
        D (fun y => (tau y : ℂ)) quadratic remainder Z0 b =
      (cmp116Eq214PhysicalTauPotential D tau quadratic remainder
        (physicalBondProjection
          (cmp116Eq223PhysicalInteriorBonds Z0)
          (Dict.flatPhysicalLinearIsometryEquiv (WithLp.toLp 2 b))) : ℂ) := by
  simp [cmp116Eq214ComplexTauPotentialCoordinate,
    cmp116Eq214PhysicalComplexTauPotential_ofReal]

end PhysicalGaugeCMP116Dictionary

end

end YangMills.RG
