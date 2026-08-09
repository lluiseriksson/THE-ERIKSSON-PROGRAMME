/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP89Eq251StabilizedBoundarySeam
import YangMills.RG.HolomorphicVerticalShiftBoundary

/-!
# One physical CMP89 coordinate contour shift

PRE-VALIDATION: source is present; its `.olean` has not yet been materialized,
and the result is not yet compiler-verified.

This module reparameterizes one Brillouin coordinate from `[-pi, pi]` as a
line of length `2*pi` starting at the lower face.  The sealed physical seam
identifies the two vertical edges, while the sealed common-strip theorem
supplies holomorphy at every point of the rectangle.  The generic
boundary-seam Cauchy theorem then shifts that single coordinate by `eta*I`.

No global periodicity of the stabilized extension is assumed.  This is one
coordinate step only: iteration over all four coordinates, the complete
strip bound `B0`, the Fourier/physical rate dictionary and window-15
attainment remain open.

Source catalog key: `cmp89.local-green.fourier.2.34-2.51`.
-/

namespace YangMills.RG

noncomputable section

/-- The physical one-coordinate line based at the lower Brillouin face.  Its
real parameter interval `[0, 2*pi]` is the translated interval
`[-pi, pi]`. -/
def cmp89Eq251PhysicalCoordinateLine
    (nu : Fin 4) (z : Fin 4 → ℂ) (w : ℂ) : Fin 4 → ℂ :=
  z + Pi.single nu w

@[simp]
theorem cmp89Eq251PhysicalCoordinateLine_zero
    (nu : Fin 4) (z : Fin 4 → ℂ) :
    cmp89Eq251PhysicalCoordinateLine nu z 0 = z := by
  simp [cmp89Eq251PhysicalCoordinateLine]

theorem cmp89Eq251PhysicalCoordinateLine_two_pi_add
    (nu : Fin 4) (z : Fin 4 → ℂ) (w : ℂ) :
    cmp89Eq251PhysicalCoordinateLine nu z
        (((2 * Real.pi : ℝ) : ℂ) + w) =
      cmp89Eq248PhysicalCoordinatePeriodShift nu
        (cmp89Eq251PhysicalCoordinateLine nu z w) := by
  funext k
  by_cases hk : k = nu
  · subst k
    simp [cmp89Eq251PhysicalCoordinateLine,
      cmp89Eq248PhysicalCoordinatePeriodShift, Pi.single_apply]
    ring
  · simp [cmp89Eq251PhysicalCoordinateLine,
      cmp89Eq248PhysicalCoordinatePeriodShift, Pi.single_apply, hk]

/-- Shift one physical Brillouin coordinate through the common analytic
strip.  The base point lies on the lower face in coordinate `nu`; that
coordinate is real before it is shifted, while previously shifted
coordinates may already have imaginary parts bounded by `rho`. -/
theorem intervalIntegral_cmp89Eq251ComplexStabilizedIntegrand_coordinateShift
    {L j : ℕ} [NeZero L] {mass a alpha rho eta : ℝ}
    (ha : 0 ≤ a) (hmassPos : 0 < mass) (hrho : 0 ≤ rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hwindow : CMP89Eq249CentralStabilizedComplexWindow a rho)
    (hmass : CMP89Eq251UniformMassWindow mass)
    (heta : |eta| ≤ rho)
    (nu mu : Fin 4) {p : Fin 4 → ℝ}
    (hp : ∀ k, |p k| ≤ Real.pi) (hface : p nu = -Real.pi)
    {z : Fin 4 → ℂ} (hreal : ∀ k, (z k).re = p k)
    (himag : ∀ k, |(z k).im| ≤ rho) (hnuImag : (z nu).im = 0)
    (holderU transportU : Fin 4 → ℤ) :
    (∫ x : ℝ in 0..2 * Real.pi,
      cmp89Eq251ComplexStabilizedIntegrand 4 L j mass a alpha
        (cmp89Eq251PhysicalCoordinateLine nu z (x : ℂ)) mu
        (cmp89Eq251LatticeDisplacement holderU)
        (cmp89Eq251LatticeDisplacement transportU)) =
      ∫ x : ℝ in 0..2 * Real.pi,
        cmp89Eq251ComplexStabilizedIntegrand 4 L j mass a alpha
          (cmp89Eq251PhysicalCoordinateLine nu z
            ((x : ℂ) + eta * Complex.I)) mu
          (cmp89Eq251LatticeDisplacement holderU)
          (cmp89Eq251LatticeDisplacement transportU) := by
  let f : ℂ → ℂ := fun w =>
    cmp89Eq251ComplexStabilizedIntegrand 4 L j mass a alpha
      (cmp89Eq251PhysicalCoordinateLine nu z w) mu
      (cmp89Eq251LatticeDisplacement holderU)
      (cmp89Eq251LatticeDisplacement transportU)
  have himag_of_mem (y : ℝ) (hy : y ∈ Set.uIcc (0 : ℝ) eta) :
      ∀ k, |(cmp89Eq251PhysicalCoordinateLine nu z
        (y * Complex.I) k).im| ≤ rho := by
    intro k
    by_cases hk : k = nu
    · subst k
      have hyAbs : |y| ≤ |eta| := by
        simpa using Set.abs_sub_left_of_mem_uIcc hy
      simpa [cmp89Eq251PhysicalCoordinateLine, Pi.single_apply,
        hnuImag] using hyAbs.trans heta
    · simpa [cmp89Eq251PhysicalCoordinateLine, Pi.single_apply, hk]
        using himag k
  have hboundary : ∀ y ∈ Set.uIcc (0 : ℝ) eta,
      f (((2 * Real.pi : ℝ) : ℂ) + y * Complex.I) =
        f (y * Complex.I) := by
    intro y hy
    have hrealY : ∀ k,
        (cmp89Eq251PhysicalCoordinateLine nu z
          (y * Complex.I) k).re = p k := by
      intro k
      by_cases hk : k = nu
      · subst k
        simp [cmp89Eq251PhysicalCoordinateLine, Pi.single_apply,
          hreal nu]
      · simp [cmp89Eq251PhysicalCoordinateLine, Pi.single_apply, hk,
          hreal k]
    have hseam :=
      cmp89Eq251ComplexStabilizedIntegrand_boundarySeam
        ha hmassPos hrho hamplitude hradius hwindow hmass nu mu hp hface
          hrealY (himag_of_mem y hy) holderU transportU
    simpa [f, cmp89Eq251PhysicalCoordinateLine_two_pi_add] using hseam
  have hdiff : DifferentiableOn ℂ f
      (Set.uIcc 0 (2 * Real.pi) ×ℂ Set.uIcc 0 eta) := by
    intro w hw
    rw [Complex.mem_reProdIm] at hw
    have hx : 0 ≤ w.re ∧ w.re ≤ 2 * Real.pi := by
      have hx' := hw.1
      rw [Set.uIcc_of_le (mul_nonneg (by norm_num) Real.pi_pos.le)] at hx'
      exact hx'
    have hyAbs : |w.im| ≤ |eta| := by
      simpa using Set.abs_sub_left_of_mem_uIcc hw.2
    let pw : Fin 4 → ℝ := fun k =>
      (cmp89Eq251PhysicalCoordinateLine nu z w k).re
    have hpw : ∀ k, |pw k| ≤ Real.pi := by
      intro k
      by_cases hk : k = nu
      · subst k
        have hbounds : -Real.pi ≤ -Real.pi + w.re ∧
            -Real.pi + w.re ≤ Real.pi := by
          constructor <;> linarith [Real.pi_pos]
        rw [abs_le]
        simpa [pw, cmp89Eq251PhysicalCoordinateLine, Pi.single_apply,
          hreal nu, hface] using hbounds
      · simpa [pw, cmp89Eq251PhysicalCoordinateLine, Pi.single_apply, hk,
          hreal k] using hp k
    have himagW : ∀ k,
        |(cmp89Eq251PhysicalCoordinateLine nu z w k).im| ≤ rho := by
      intro k
      by_cases hk : k = nu
      · subst k
        simpa [cmp89Eq251PhysicalCoordinateLine, Pi.single_apply,
          hnuImag] using hyAbs.trans heta
      · simpa [cmp89Eq251PhysicalCoordinateLine, Pi.single_apply, hk]
          using himag k
    have houter : DifferentiableAt ℂ
        (fun q : Fin 4 → ℂ =>
          cmp89Eq251ComplexStabilizedIntegrand 4 L j mass a alpha q mu
            (cmp89Eq251LatticeDisplacement holderU)
            (cmp89Eq251LatticeDisplacement transportU))
        (cmp89Eq251PhysicalCoordinateLine nu z w) :=
      differentiableAt_cmp89Eq251ComplexStabilizedIntegrand_of_commonRadius
        ha hmassPos hrho hamplitude hradius hwindow hmass hpw
          (fun _ => rfl) himagW
    have hinner : DifferentiableAt ℂ
        (cmp89Eq251PhysicalCoordinateLine nu z) w := by
      unfold cmp89Eq251PhysicalCoordinateLine
      fun_prop
    simpa [f] using (houter.comp w hinner).differentiableWithinAt
  exact intervalIntegral_eq_verticalShift_of_boundary_eq_of_differentiableOn
    f (2 * Real.pi) eta hboundary hdiff

end

end YangMills.RG
