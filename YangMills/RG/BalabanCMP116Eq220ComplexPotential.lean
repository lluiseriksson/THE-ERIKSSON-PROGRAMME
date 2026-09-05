/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116Eq214ComplexTauPotential

/-!
# CMP116 equation (2.20) on the complex tau contour

The localized potentials `V_k(Y,B)` are real, while their Cauchy parameters
`tau(Y)` are complex.  Consequently, the real part of the literal potential
depends on `Re tau(Y)`.  This module derives the uniform contour bound from the
already source-faithful real equation-(2.20) theorem and the elementary
inequality `|Re z| ≤ ‖z‖`.

The conclusion is a bound on the real part of the literal complex potential;
it does not assume a bound on an arbitrary complex scalar field.
-/

namespace YangMills.RG

open Matrix
open scoped BigOperators RealInnerProductSpace

noncomputable section

private abbrev PhysicalEndomorphism (d N Nc : ℕ) [NeZero N] :=
  PhysicalGaugeOneCochain d N Nc →L[ℝ]
    PhysicalGaugeOneCochain d N Nc

/-- The quadratic contribution on a centered Cauchy circle splits into a
center kernel and a displacement kernel.

The center coefficient costs at most one copy of the raw kernel.  The
displacement is controlled by the kernel of `radius • Q`.  Thus no invalid
replacement `‖z‖ ≤ radius` is used. -/
theorem cmp116Eq220_centeredQuadratic_le_localized
    {d N Nc : ℕ} [NeZero N]
    (Y0 : Finset (PhysicalBond d N))
    (Q : PhysicalEndomorphism d N Nc)
    (B : PhysicalGaugeOneCochain d N Nc)
    (rate rowSum centerAmplitude displacementAmplitude radius : ℝ)
    {s : ℝ} {z : ℂ}
    (hs : s ∈ Set.uIoc (0 : ℝ) 1)
    (hz : ‖z - (s : ℂ)‖ ≤ radius)
    (hradius : 0 ≤ radius)
    (hrow : ∀ target : PhysicalBond d N,
      ∑ source : PhysicalBond d N,
        Real.exp (-(rate * (physicalBondDist target source : ℝ))) ≤ rowSum)
    (hsupport : ∀ i, i ∉ Y0 → B i = 0)
    (hcenter :
      PhysicalCovarianceExponentialKernelBound
        Q physicalBondDist centerAmplitude rate)
    (hdisplacement :
      PhysicalCovarianceExponentialKernelBound
        (radius • Q) physicalBondDist displacementAmplitude rate) :
    ‖z‖ * |inner ℝ B (Q B)| ≤
      (centerAmplitude + displacementAmplitude) * rowSum *
        (∑ i ∈ Y0, ‖B i‖ ^ 2) := by
  have hs0 : 0 < s := by simpa using hs.1
  have hs1 : s ≤ 1 := by simpa using hs.2
  have hcenterNorm : ‖(s : ℂ)‖ ≤ 1 := by
    simpa [abs_of_pos hs0] using hs1
  have hznorm : ‖z‖ ≤ 1 + radius := by
    calc
      ‖z‖ = ‖(z - (s : ℂ)) + (s : ℂ)‖ := by rw [sub_add_cancel]
      _ ≤ ‖z - (s : ℂ)‖ + ‖(s : ℂ)‖ := norm_add_le _ _
      _ ≤ radius + 1 := add_le_add hz hcenterNorm
      _ = 1 + radius := by ring
  have hcenterForm :=
    physicalExponentialKernel_quadratic_form_le_localized
      Y0 Q hcenter hrow B hsupport
  have hdisplacementForm :=
    physicalExponentialKernel_quadratic_form_le_localized
      Y0 (radius • Q) hdisplacement hrow B hsupport
  have hscaled :
      |inner ℝ B ((radius • Q) B)| =
        radius * |inner ℝ B (Q B)| := by
    change |inner ℝ B (radius • Q B)| = _
    rw [inner_smul_right, abs_mul, abs_of_nonneg hradius]
  calc
    ‖z‖ * |inner ℝ B (Q B)| ≤
        (1 + radius) * |inner ℝ B (Q B)| :=
      mul_le_mul_of_nonneg_right hznorm (abs_nonneg _)
    _ = |inner ℝ B (Q B)| +
        |inner ℝ B ((radius • Q) B)| := by
      rw [hscaled]
      ring
    _ ≤ centerAmplitude * rowSum * (∑ i ∈ Y0, ‖B i‖ ^ 2) +
        displacementAmplitude * rowSum * (∑ i ∈ Y0, ‖B i‖ ^ 2) :=
      add_le_add hcenterForm hdisplacementForm
    _ = (centerAmplitude + displacementAmplitude) * rowSum *
        (∑ i ∈ Y0, ‖B i‖ ^ 2) := by ring

/-- Complex-contour form of equation (2.20).  The contour dependence enters
through `‖tau(Y)‖`; the quadratic kernel and the residual term remain the
literal two pieces of equation (1.42). -/
theorem cmp116Eq220_re_physicalComplexTauPotential_le_localized
    {Y : Type*} [DecidableEq Y]
    {d N Nc : ℕ} [NeZero N]
    (D : Finset Y) (Y0 : Finset (PhysicalBond d N))
    (tau : Y → ℂ)
    (quadratic : Y → PhysicalGaugeOneCochain d N Nc →
      PhysicalEndomorphism d N Nc)
    (remainder : Y → PhysicalGaugeOneCochain d N Nc → ℝ)
    (amplitude residualWeight : Y → ℝ)
    {kappa rowSum : ℝ}
    (hrowSum : 0 ≤ rowSum)
    (hrow : ∀ target : PhysicalBond d N,
      ∑ source : PhysicalBond d N,
        Real.exp (-(kappa * (physicalBondDist target source : ℝ))) ≤ rowSum)
    (B : PhysicalGaugeOneCochain d N Nc)
    (hsupport : ∀ i, i ∉ Y0 → B i = 0)
    (hquadratic : ∀ y ∈ D,
      PhysicalCovarianceExponentialKernelBound
        (quadratic y B) physicalBondDist (amplitude y) kappa)
    (hremainder : ∀ y ∈ D,
      ‖tau y‖ * |remainder y B| ≤ residualWeight y) :
    (cmp116Eq214PhysicalComplexTauPotential
        D tau quadratic remainder B).re ≤
      (∑ y ∈ D, ‖tau y‖ * amplitude y * rowSum) / 2 *
          (∑ i ∈ Y0, ‖B i‖ ^ 2) +
        ∑ y ∈ D, residualWeight y := by
  have hremainderRe : ∀ y ∈ D,
      |(tau y).re| * |remainder y B| ≤ residualWeight y := by
    intro y hy
    exact le_trans
      (mul_le_mul_of_nonneg_right
        (Complex.abs_re_le_norm (tau y)) (abs_nonneg _))
      (hremainder y hy)
  have hreal := cmp116Eq220_physicalTauPotential_le_localized
    D Y0 (fun y => (tau y).re) quadratic remainder amplitude residualWeight
    hrow B hsupport hquadratic hremainderRe
  have hcoeff :
      (∑ y ∈ D, |(tau y).re| * amplitude y * rowSum) ≤
        ∑ y ∈ D, ‖tau y‖ * amplitude y * rowSum := by
    apply Finset.sum_le_sum
    intro y hy
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (Complex.abs_re_le_norm (tau y))
        (hquadratic y hy).1)
      hrowSum
  have henergy : 0 ≤ ∑ i ∈ Y0, ‖B i‖ ^ 2 := by positivity
  calc
    (cmp116Eq214PhysicalComplexTauPotential
        D tau quadratic remainder B).re =
        cmp116Eq214PhysicalTauPotential
          D (fun y => (tau y).re) quadratic remainder B := by
            simp [cmp116Eq214PhysicalComplexTauPotential_re,
              cmp116Eq214PhysicalTauPotential]
    _ ≤ (∑ y ∈ D, |(tau y).re| * amplitude y * rowSum) / 2 *
          (∑ i ∈ Y0, ‖B i‖ ^ 2) +
        ∑ y ∈ D, residualWeight y := hreal
    _ ≤ (∑ y ∈ D, ‖tau y‖ * amplitude y * rowSum) / 2 *
          (∑ i ∈ Y0, ‖B i‖ ^ 2) +
        ∑ y ∈ D, residualWeight y := by
          gcongr

/-- Uniform polydisc version of complex equation (2.20).  The contour point
`tau` disappears from the majorant in favor of the source Cauchy radii. -/
theorem cmp116Eq220_re_physicalComplexTauPotential_le_localized_polydisc
    {Y : Type*} [DecidableEq Y]
    {d N Nc : ℕ} [NeZero N]
    (D : Finset Y) (Y0 : Finset (PhysicalBond d N))
    (tau : Y → ℂ) (radius : Y → ℝ)
    (quadratic : Y → PhysicalGaugeOneCochain d N Nc →
      PhysicalEndomorphism d N Nc)
    (remainder : Y → PhysicalGaugeOneCochain d N Nc → ℝ)
    (amplitude residualWeight : Y → ℝ)
    {kappa rowSum : ℝ}
    (hrowSum : 0 ≤ rowSum)
    (hrow : ∀ target : PhysicalBond d N,
      ∑ source : PhysicalBond d N,
        Real.exp (-(kappa * (physicalBondDist target source : ℝ))) ≤ rowSum)
    (B : PhysicalGaugeOneCochain d N Nc)
    (hsupport : ∀ i, i ∉ Y0 → B i = 0)
    (htau : ∀ y ∈ D, ‖tau y‖ ≤ radius y)
    (hquadratic : ∀ y ∈ D,
      PhysicalCovarianceExponentialKernelBound
        (quadratic y B) physicalBondDist (amplitude y) kappa)
    (hremainder : ∀ y ∈ D,
      radius y * |remainder y B| ≤ residualWeight y) :
    (cmp116Eq214PhysicalComplexTauPotential
        D tau quadratic remainder B).re ≤
      (∑ y ∈ D, radius y * amplitude y * rowSum) / 2 *
          (∑ i ∈ Y0, ‖B i‖ ^ 2) +
        ∑ y ∈ D, residualWeight y := by
  have hremainderTau : ∀ y ∈ D,
      ‖tau y‖ * |remainder y B| ≤ residualWeight y := by
    intro y hy
    exact le_trans
      (mul_le_mul_of_nonneg_right (htau y hy) (abs_nonneg _))
      (hremainder y hy)
  have hcomplex :=
    cmp116Eq220_re_physicalComplexTauPotential_le_localized
      D Y0 tau quadratic remainder amplitude residualWeight
      hrowSum hrow B hsupport hquadratic hremainderTau
  have hcoeff :
      (∑ y ∈ D, ‖tau y‖ * amplitude y * rowSum) ≤
        ∑ y ∈ D, radius y * amplitude y * rowSum := by
    apply Finset.sum_le_sum
    intro y hy
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (htau y hy) (hquadratic y hy).1)
      hrowSum
  have henergy : 0 ≤ ∑ i ∈ Y0, ‖B i‖ ^ 2 := by positivity
  exact hcomplex.trans (by gcongr)

namespace PhysicalGaugeCMP116Dictionary

/-- Coordinate-facing complex equation-(2.20) estimate.  The physical field
is constructed from the finite Gaussian coordinate and localized by the
canonical projector of `Z0`; its energy is then rewritten as the exact scalar
quadratic form of that projector. -/
theorem re_cmp116Eq214ComplexTauPotentialCoordinate_le_projection
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
    (b : CMP116Eq214GaussianCoordinate (Cube d L) lieDim)
    (hquadratic : ∀ y ∈ D,
      PhysicalCovarianceExponentialKernelBound
        (quadratic y
          (physicalBondProjection
            (cmp116Eq223PhysicalInteriorBonds Z0)
            (Dict.flatPhysicalLinearIsometryEquiv (WithLp.toLp 2 b))))
        physicalBondDist (amplitude y) kappa)
    (hremainder : ∀ y ∈ D,
      ‖tau y‖ *
          |remainder y
            (physicalBondProjection
              (cmp116Eq223PhysicalInteriorBonds Z0)
              (Dict.flatPhysicalLinearIsometryEquiv (WithLp.toLp 2 b)))| ≤
        residualWeight y) :
    (Dict.cmp116Eq214ComplexTauPotentialCoordinate
        D tau quadratic remainder Z0 b).re ≤
      (∑ y ∈ D, ‖tau y‖ * amplitude y * rowSum) / 2 *
          ((WithLp.toLp 2 b) ⬝ᵥ
            (cmp116Eq223CoordinateProjection
              (Dict.cmp116Eq223PhysicalLocalizedCoordinates Z0) *ᵥ
                (WithLp.toLp 2 b))) +
        ∑ y ∈ D, residualWeight y := by
  let S : Finset (PhysicalBond d (M * N')) :=
    cmp116Eq223PhysicalInteriorBonds Z0
  let bLp : EuclideanSpace ℝ (CMP116CoordIndex d L lieDim) :=
    WithLp.toLp 2 b
  let B : PhysicalGaugeOneCochain d (M * N') Nc :=
    physicalBondProjection S (Dict.flatPhysicalLinearIsometryEquiv bLp)
  have hsupport : ∀ i, i ∉ S → B i = 0 := by
    intro i hi
    exact physicalBondProjection_apply_not_mem S hi _
  have hphysical :=
    cmp116Eq220_re_physicalComplexTauPotential_le_localized
      D S tau quadratic remainder amplitude residualWeight
      hrowSum hrow B hsupport hquadratic hremainder
  have henergy :
      (∑ i ∈ S, ‖B i‖ ^ 2) =
        bLp ⬝ᵥ
          (cmp116Eq223CoordinateProjection
            (Dict.cmp116Eq223PhysicalLocalizedCoordinates Z0) *ᵥ bLp) := by
    calc
      (∑ i ∈ S, ‖B i‖ ^ 2) =
          ∑ i ∈ S, ‖Dict.flatPhysicalLinearIsometryEquiv bLp i‖ ^ 2 := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [physicalBondProjection_apply_mem S hi]
      _ = bLp ⬝ᵥ
          (cmp116Eq223CoordinateProjection
            (Dict.cmp116Eq223PhysicalLocalizedCoordinates Z0) *ᵥ bLp) := by
            simpa [S] using
              Dict.sum_norm_sq_flatPhysicalLinearIsometryEquiv_physicalInteriorBonds_eq_dotProduct
                Z0 bLp
  simpa [cmp116Eq214ComplexTauPotentialCoordinate, S, bLp, B, henergy]
    using hphysical

end PhysicalGaugeCMP116Dictionary

end

end YangMills.RG
