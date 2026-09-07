/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116Eq221PhysicalInteractionExponent

/-!
# The literal CMP116 potential and equation (2.20)

Balaban's equation (2.20) does not estimate an isolated Wilson Hessian.  It
estimates the real `tau`-weighted potential from equation (2.14), after using
the source decomposition (1.42)

`V_k(Y,B) = (1/2) <B, Q(Y,B) B> + V''_k(Y,B)`.

This module records that decomposition literally and proves the finite
resummation step.  A block-kernel estimate for every localized quadratic
operator and a separate bound for the residual terms imply the localized
quadratic estimate required by the `alpha5` ledger.  The terminal theorem
constructs the potential internally, so it has neither an arbitrary
`potential` function nor an `hpotential` premise.

Honest scope: the source dictionaries constructing `D`, `tau`, `Q`, and
`V''_k` from Balaban's localized fluctuation action remain explicit inputs.
In particular, this module does not rename the missing equations (1.36),
(1.43), (2.18), or the localization-domain resummation as a scalar potential
bound.
-/

namespace YangMills.RG

open Matrix
open scoped BigOperators RealInnerProductSpace

noncomputable section

private abbrev PhysicalEndomorphism (d N Nc : ℕ) [NeZero N] :=
  PhysicalGaugeOneCochain d N Nc →L[ℝ]
    PhysicalGaugeOneCochain d N Nc

/-- The literal two-piece potential term in CMP116 equation (1.42).  The
quadratic operator is allowed to depend on the fluctuation field, as it does
in the source. -/
noncomputable def cmp116Eq142PhysicalPotentialTerm
    {Y : Type*} {d N Nc : ℕ} [NeZero N]
    (quadratic : Y → PhysicalGaugeOneCochain d N Nc →
      PhysicalEndomorphism d N Nc)
    (remainder : Y → PhysicalGaugeOneCochain d N Nc → ℝ)
    (y : Y) (B : PhysicalGaugeOneCochain d N Nc) : ℝ :=
  (1 / 2 : ℝ) * inner ℝ B (quadratic y B B) + remainder y B

/-- The real, finite `tau`-weighted potential appearing in equation (2.14).
The complex Cauchy-contour version is deliberately not identified here. -/
noncomputable def cmp116Eq214PhysicalTauPotential
    {Y : Type*} [DecidableEq Y]
    {d N Nc : ℕ} [NeZero N]
    (D : Finset Y) (tau : Y → ℝ)
    (quadratic : Y → PhysicalGaugeOneCochain d N Nc →
      PhysicalEndomorphism d N Nc)
    (remainder : Y → PhysicalGaugeOneCochain d N Nc → ℝ)
    (B : PhysicalGaugeOneCochain d N Nc) : ℝ :=
  ∑ y ∈ D, tau y * cmp116Eq142PhysicalPotentialTerm quadratic remainder y B

/-- Source-faithful finite form of equation (2.20).  The quadratic and
residual pieces of (1.42) are bounded independently before the `D`-sum is
performed.  Thus the conclusion is a derived potential estimate, not an
assumed scalar majorant. -/
theorem cmp116Eq220_physicalTauPotential_le_localized
    {Y : Type*} [DecidableEq Y]
    {d N Nc : ℕ} [NeZero N]
    (D : Finset Y) (Y0 : Finset (PhysicalBond d N))
    (tau : Y → ℝ)
    (quadratic : Y → PhysicalGaugeOneCochain d N Nc →
      PhysicalEndomorphism d N Nc)
    (remainder : Y → PhysicalGaugeOneCochain d N Nc → ℝ)
    (amplitude residualWeight : Y → ℝ)
    {kappa rowSum : ℝ}
    (hrow : ∀ target : PhysicalBond d N,
      ∑ source : PhysicalBond d N,
        Real.exp (-(kappa * (physicalBondDist target source : ℝ))) ≤ rowSum)
    (B : PhysicalGaugeOneCochain d N Nc)
    (hsupport : ∀ i, i ∉ Y0 → B i = 0)
    (hquadratic : ∀ y ∈ D,
      PhysicalCovarianceExponentialKernelBound
        (quadratic y B) physicalBondDist (amplitude y) kappa)
    (hremainder : ∀ y ∈ D,
      |tau y| * |remainder y B| ≤ residualWeight y) :
    cmp116Eq214PhysicalTauPotential D tau quadratic remainder B ≤
      (∑ y ∈ D, |tau y| * amplitude y * rowSum) / 2 *
          (∑ i ∈ Y0, ‖B i‖ ^ 2) +
        ∑ y ∈ D, residualWeight y := by
  let energy : ℝ := ∑ i ∈ Y0, ‖B i‖ ^ 2
  have hterm : ∀ y ∈ D,
      tau y * cmp116Eq142PhysicalPotentialTerm quadratic remainder y B ≤
        (|tau y| * amplitude y * rowSum) / 2 * energy +
          residualWeight y := by
    intro y hy
    have hquad := physicalExponentialKernel_quadratic_form_le_localized
      Y0 (quadratic y B) (hquadratic y hy) hrow B hsupport
    have htermAbs :
        |cmp116Eq142PhysicalPotentialTerm quadratic remainder y B| ≤
          (1 / 2 : ℝ) * |inner ℝ B (quadratic y B B)| +
            |remainder y B| := by
      dsimp [cmp116Eq142PhysicalPotentialTerm]
      calc
        |(1 / 2 : ℝ) * inner ℝ B (quadratic y B B) + remainder y B| ≤
            |(1 / 2 : ℝ) * inner ℝ B (quadratic y B B)| +
              |remainder y B| := abs_add_le _ _
        _ = (1 / 2 : ℝ) * |inner ℝ B (quadratic y B B)| +
              |remainder y B| := by norm_num [abs_mul]
    calc
      tau y * cmp116Eq142PhysicalPotentialTerm quadratic remainder y B ≤
          |tau y * cmp116Eq142PhysicalPotentialTerm quadratic remainder y B| :=
        le_abs_self _
      _ = |tau y| *
          |cmp116Eq142PhysicalPotentialTerm quadratic remainder y B| :=
        abs_mul _ _
      _ ≤ |tau y| *
          ((1 / 2 : ℝ) * |inner ℝ B (quadratic y B B)| +
            |remainder y B|) :=
        mul_le_mul_of_nonneg_left htermAbs (abs_nonneg _)
      _ ≤ |tau y| *
          ((1 / 2 : ℝ) * (amplitude y * rowSum * energy) +
            |remainder y B|) := by
        gcongr
      _ = (|tau y| * amplitude y * rowSum) / 2 * energy +
          |tau y| * |remainder y B| := by ring
      _ ≤ (|tau y| * amplitude y * rowSum) / 2 * energy +
          residualWeight y := add_le_add_right (hremainder y hy) _
  have hsum := Finset.sum_le_sum hterm
  calc
    cmp116Eq214PhysicalTauPotential D tau quadratic remainder B =
        ∑ y ∈ D,
          tau y * cmp116Eq142PhysicalPotentialTerm quadratic remainder y B := rfl
    _ ≤ ∑ y ∈ D,
        ((|tau y| * amplitude y * rowSum) / 2 * energy +
          residualWeight y) := hsum
    _ = (∑ y ∈ D, |tau y| * amplitude y * rowSum) / 2 * energy +
        ∑ y ∈ D, residualWeight y := by
      rw [Finset.sum_add_distrib]
      congr 1
      calc
        (∑ y ∈ D, (|tau y| * amplitude y * rowSum) / 2 * energy) =
            ∑ y ∈ D,
              (|tau y| * amplitude y * rowSum) * (energy / 2) := by
                apply Finset.sum_congr rfl
                intro y _
                ring
        _ = (∑ y ∈ D, |tau y| * amplitude y * rowSum) *
              (energy / 2) := by rw [Finset.sum_mul]
        _ = (∑ y ∈ D, |tau y| * amplitude y * rowSum) / 2 *
              energy := by ring

/-- The strongest real `alpha5` endpoint with the CMP116 potential built
literally from (1.42) and (2.14).  No arbitrary potential function and no
scalar `hpotential` premise remain. -/
theorem CMP116Eq216PhysicalKernelCertificate.physicalRealInteractionExponent_le_coordinateAlpha5_of_eq220Source
    {Y : Type*} [DecidableEq Y]
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
    (D : Finset Y) (tau : Y → ℝ)
    (quadratic : Y → PhysicalGaugeOneCochain d (M * N') Nc →
      PhysicalEndomorphism d (M * N') Nc)
    (remainder : Y → PhysicalGaugeOneCochain d (M * N') Nc → ℝ)
    (amplitude residualWeight : Y → ℝ)
    {potentialKappa potentialRowSum cutoff alpha5 : ℝ}
    (hpotentialRowSum : 0 ≤ potentialRowSum)
    (hpotentialRow : ∀ target : PhysicalBond d (M * N'),
      ∑ source : PhysicalBond d (M * N'),
        Real.exp (-(potentialKappa *
          (physicalBondDist target source : ℝ))) ≤ potentialRowSum)
    (hquadratic : ∀ y ∈ D,
      PhysicalCovarianceExponentialKernelBound
        (quadratic y
          (physicalBondProjection
            (PhysicalGaugeCMP116Dictionary.cmp116Eq223PhysicalInteriorBonds Z0)
            (Dict.flatPhysicalLinearIsometryEquiv b)))
        physicalBondDist (amplitude y) potentialKappa)
    (hremainder : ∀ y ∈ D,
      |tau y| *
          |remainder y
            (physicalBondProjection
              (PhysicalGaugeCMP116Dictionary.cmp116Eq223PhysicalInteriorBonds Z0)
              (Dict.flatPhysicalLinearIsometryEquiv b))| ≤
        residualWeight y)
    (hcutoff : 0 ≤ cutoff)
    (hbudget :
      (∑ y ∈ D, |tau y| * amplitude y * potentialRowSum) +
          2 * (cert.amplitude *
            cmp116Eq221PhysicalRowSum d cert.rate) +
          cutoff ≤ alpha5) :
    Dict.cmp116Eq221PhysicalRealInteractionExponent
          Z0 R₁ R₂ R₃
          (cmp116Eq214PhysicalTauPotential D tau quadratic remainder) x b +
        cutoff / 2 *
          (∑ qa ∈ Dict.cmp116Eq222SelectedCoordinates P, b qa ^ 2) ≤
      alpha5 / 2 *
          (x ⬝ᵥ
              (cmp116Eq223CoordinateProjection
                (Dict.cmp116Eq223PhysicalLocalizedCoordinates Z0) *ᵥ x) +
            b ⬝ᵥ
              (cmp116Eq223CoordinateProjection
                (Dict.cmp116Eq223PhysicalLocalizedCoordinates Z0) *ᵥ b)) +
        ∑ y ∈ D, residualWeight y := by
  let S : Finset (PhysicalBond d (M * N')) :=
    PhysicalGaugeCMP116Dictionary.cmp116Eq223PhysicalInteriorBonds Z0
  let B : PhysicalGaugeOneCochain d (M * N') Nc :=
    physicalBondProjection S (Dict.flatPhysicalLinearIsometryEquiv b)
  have hsupport : ∀ i, i ∉ S → B i = 0 := by
    intro i hi
    exact physicalBondProjection_apply_not_mem S hi _
  have hpotential := cmp116Eq220_physicalTauPotential_le_localized
    D S tau quadratic remainder amplitude residualWeight
    hpotentialRow B hsupport hquadratic hremainder
  have henergy :
      (∑ i ∈ S, ‖B i‖ ^ 2) =
        b ⬝ᵥ
          (cmp116Eq223CoordinateProjection
            (Dict.cmp116Eq223PhysicalLocalizedCoordinates Z0) *ᵥ b) := by
    calc
      (∑ i ∈ S, ‖B i‖ ^ 2) =
          ∑ i ∈ S, ‖Dict.flatPhysicalLinearIsometryEquiv b i‖ ^ 2 := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [physicalBondProjection_apply_mem S hi]
      _ = b ⬝ᵥ
          (cmp116Eq223CoordinateProjection
            (Dict.cmp116Eq223PhysicalLocalizedCoordinates Z0) *ᵥ b) := by
            simpa [S] using
              Dict.sum_norm_sq_flatPhysicalLinearIsometryEquiv_physicalInteriorBonds_eq_dotProduct
                Z0 b
  apply cert.physicalRealInteractionExponent_le_coordinateAlpha5_physicalCutoff_geometric
    Dict Dset P Z0 hZ0 hgeom x b
    (potential := cmp116Eq214PhysicalTauPotential D tau quadratic remainder)
    (potentialRate :=
      ∑ y ∈ D, |tau y| * amplitude y * potentialRowSum)
    (residual20 := ∑ y ∈ D, residualWeight y)
  · rw [henergy] at hpotential
    exact hpotential
  · refine Finset.sum_nonneg ?_
    intro y hy
    exact mul_nonneg
      (mul_nonneg (abs_nonneg _) (hquadratic y hy).1)
      hpotentialRowSum
  · exact hcutoff
  · exact hbudget

end

end YangMills.RG
