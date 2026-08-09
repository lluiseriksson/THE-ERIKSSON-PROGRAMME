/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP89Eq251StabilizedEndpointOneCoordinateContourShift
import YangMills.RG.IntervalIntegralPiCoordinateTransport

/-!
# PRE-VALIDATION: compact product integrability for one shifted CMP89 endpoint

The source in this module is present, but its `.olean` has not yet been
materialized and its result has not yet been verified by the Lean compiler.

This module constructs the partially signed physical momentum used when the
four Brillouin coordinates are shifted in order.  Stage `r` shifts exactly
the coordinates `nu` with `nu.val < r`.  Common-strip endpoint holomorphy then
produces continuity on the compact real parameter cube and hence integrability
under the literal product of four restricted interval measures.

No family of endpoint functions, integrability premise, complete contour
equality, bound `B0`, owner dictionary or window-15 conclusion is accepted.
-/

namespace YangMills.RG

open MeasureTheory

noncomputable section

/-- Translate the parameter cube `[0,2*pi]^4` to the physical Brillouin cube
`[-pi,pi]^4`. -/
def cmp89Eq251PhysicalBrillouinParameter
    (x : Fin 4 → ℝ) : Fin 4 → ℝ :=
  fun nu => -Real.pi + x nu

/-- Shift exactly the first `stage` coordinates in the endpoint-specific
signed imaginary direction. -/
def cmp89Eq251EndpointPartialSignedContourMomentum
    (stage : ℕ) (rho : ℝ) (x : Fin 4 → ℝ)
    (endpointDisplacement : Fin 4 → ℝ) : Fin 4 → ℂ :=
  fun nu => if nu.val < stage then
      cmp89Eq251SignedContourMomentum rho
        (cmp89Eq251PhysicalBrillouinParameter x) endpointDisplacement nu
    else
      (cmp89Eq251PhysicalBrillouinParameter x nu : ℂ)

@[simp]
theorem cmp89Eq251EndpointPartialSignedContourMomentum_re
    (stage : ℕ) (rho : ℝ) (x endpointDisplacement : Fin 4 → ℝ)
    (nu : Fin 4) :
    (cmp89Eq251EndpointPartialSignedContourMomentum
      stage rho x endpointDisplacement nu).re =
      cmp89Eq251PhysicalBrillouinParameter x nu := by
  by_cases hnu : nu.val < stage <;>
    simp [cmp89Eq251EndpointPartialSignedContourMomentum, hnu]

@[simp]
theorem cmp89Eq251EndpointPartialSignedContourMomentum_im
    (stage : ℕ) (rho : ℝ) (x endpointDisplacement : Fin 4 → ℝ)
    (nu : Fin 4) :
    (cmp89Eq251EndpointPartialSignedContourMomentum
      stage rho x endpointDisplacement nu).im =
      if nu.val < stage then
        rho * (SignType.sign (endpointDisplacement nu) : ℝ) else 0 := by
  by_cases hnu : nu.val < stage <;>
    simp [cmp89Eq251EndpointPartialSignedContourMomentum, hnu]

/-- Every partial stage stays in the same closed coordinate strip. -/
theorem abs_im_cmp89Eq251EndpointPartialSignedContourMomentum_le
    {rho : ℝ} (hrho : 0 ≤ rho) (stage : ℕ)
    (x endpointDisplacement : Fin 4 → ℝ) (nu : Fin 4) :
    |(cmp89Eq251EndpointPartialSignedContourMomentum
      stage rho x endpointDisplacement nu).im| ≤ rho := by
  by_cases hnu : nu.val < stage
  · simp only [cmp89Eq251EndpointPartialSignedContourMomentum_im, hnu,
      if_true]
    have hsign : |(SignType.sign (endpointDisplacement nu) : ℝ)| ≤ 1 := by
      rw [sign_apply]
      split_ifs <;> norm_num
    rw [abs_mul, abs_of_nonneg hrho]
    simpa using mul_le_mul_of_nonneg_left hsign hrho
  · simp [cmp89Eq251EndpointPartialSignedContourMomentum_im, hnu, hrho]

/-- The partial signed momentum depends continuously on the real cube
parameter. -/
theorem continuous_cmp89Eq251EndpointPartialSignedContourMomentum
    (stage : ℕ) (rho : ℝ) (endpointDisplacement : Fin 4 → ℝ) :
    Continuous (fun x : Fin 4 → ℝ =>
      cmp89Eq251EndpointPartialSignedContourMomentum
        stage rho x endpointDisplacement) := by
  apply continuous_pi
  intro nu
  by_cases hnu : nu.val < stage
  · simp only [cmp89Eq251EndpointPartialSignedContourMomentum, hnu,
      if_true, cmp89Eq251SignedContourMomentum,
      cmp89Eq251PhysicalBrillouinParameter]
    fun_prop
  · simp only [cmp89Eq251EndpointPartialSignedContourMomentum, hnu,
      if_false, cmp89Eq251PhysicalBrillouinParameter]
    fun_prop

@[simp]
theorem cmp89Eq251EndpointPartialSignedContourMomentum_zero
    (rho : ℝ) (x endpointDisplacement : Fin 4 → ℝ) :
    cmp89Eq251EndpointPartialSignedContourMomentum
        0 rho x endpointDisplacement =
      fun nu => (cmp89Eq251PhysicalBrillouinParameter x nu : ℂ) := by
  funext nu
  simp [cmp89Eq251EndpointPartialSignedContourMomentum]

@[simp]
theorem cmp89Eq251EndpointPartialSignedContourMomentum_four
    (rho : ℝ) (x endpointDisplacement : Fin 4 → ℝ) :
    cmp89Eq251EndpointPartialSignedContourMomentum
        4 rho x endpointDisplacement =
      cmp89Eq251SignedContourMomentum rho
        (cmp89Eq251PhysicalBrillouinParameter x) endpointDisplacement := by
  funext nu
  simp [cmp89Eq251EndpointPartialSignedContourMomentum, nu.isLt]

/-- Every partial endpoint contour is integrable on the compact product
Brillouin cube.  Integrability is produced from the common-strip physical
holomorphy rather than accepted as a premise. -/
theorem integrable_cmp89Eq251ComplexStabilizedEndpointIntegrand_partialSigned
    {L j : ℕ} [NeZero L] {mass a alpha rho : ℝ}
    (ha : 0 ≤ a) (hmassPos : 0 < mass) (hrho : 0 ≤ rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hwindow : CMP89Eq249CentralStabilizedComplexWindow a rho)
    (hmass : CMP89Eq251UniformMassWindow mass)
    (stage : ℕ) (mu : Fin 4)
    (holderDisplacement endpointDisplacement : Fin 4 → ℝ) :
    Integrable (fun x : Fin 4 → ℝ =>
      cmp89Eq251ComplexStabilizedEndpointIntegrand 4 L j mass a alpha
        (cmp89Eq251EndpointPartialSignedContourMomentum
          stage rho x endpointDisplacement)
        mu holderDisplacement endpointDisplacement)
      (Measure.pi fun _ : Fin 4 =>
        volume.restrict (Set.uIoc 0 (2 * Real.pi))) := by
  have htwoPi : (0 : ℝ) ≤ 2 * Real.pi :=
    mul_nonneg (by norm_num) Real.pi_pos.le
  have hcont : ContinuousOn (fun x : Fin 4 → ℝ =>
      cmp89Eq251ComplexStabilizedEndpointIntegrand 4 L j mass a alpha
        (cmp89Eq251EndpointPartialSignedContourMomentum
          stage rho x endpointDisplacement)
        mu holderDisplacement endpointDisplacement)
      (Set.Icc (fun _ : Fin 4 => 0) (fun _ => 2 * Real.pi)) := by
    intro x hx
    have hp : ∀ nu,
        |cmp89Eq251PhysicalBrillouinParameter x nu| ≤ Real.pi := by
      intro nu
      rw [abs_le]
      have hxLower := hx.1 nu
      have hxUpper := hx.2 nu
      simp only [cmp89Eq251PhysicalBrillouinParameter]
      constructor <;> linarith [Real.pi_pos]
    have houter :=
      differentiableAt_cmp89Eq251ComplexStabilizedEndpointIntegrand_of_commonRadius
        (L := L) (j := j) (mass := mass) (a := a) (alpha := alpha) (rho := rho)
        ha hmassPos hrho hamplitude hradius hwindow hmass
        hp
        (cmp89Eq251EndpointPartialSignedContourMomentum_re
          stage rho x endpointDisplacement)
        (abs_im_cmp89Eq251EndpointPartialSignedContourMomentum_le
          hrho stage x endpointDisplacement)
        (mu := mu)
        (holderDisplacement := holderDisplacement)
        (endpointDisplacement := endpointDisplacement)
    exact (houter.continuousAt.comp x
      (continuous_cmp89Eq251EndpointPartialSignedContourMomentum
        stage rho endpointDisplacement).continuousAt).continuousWithinAt
  have hIcc : IntegrableOn (fun x : Fin 4 → ℝ =>
      cmp89Eq251ComplexStabilizedEndpointIntegrand 4 L j mass a alpha
        (cmp89Eq251EndpointPartialSignedContourMomentum
          stage rho x endpointDisplacement)
        mu holderDisplacement endpointDisplacement)
      (Set.Icc (fun _ : Fin 4 => 0) (fun _ => 2 * Real.pi))
      (volume : Measure (Fin 4 → ℝ)) :=
    hcont.integrableOn_compact
      (isCompact_Icc : IsCompact
        (Set.Icc (fun _ : Fin 4 => 0) (fun _ => 2 * Real.pi)))
  have hIoc : IntegrableOn (fun x : Fin 4 → ℝ =>
      cmp89Eq251ComplexStabilizedEndpointIntegrand 4 L j mass a alpha
        (cmp89Eq251EndpointPartialSignedContourMomentum
          stage rho x endpointDisplacement)
        mu holderDisplacement endpointDisplacement)
      (Set.univ.pi fun _ : Fin 4 => Set.Ioc 0 (2 * Real.pi))
      (volume : Measure (Fin 4 → ℝ)) :=
    hIcc.congr_set_ae Measure.univ_pi_Ioc_ae_eq_Icc
  rw [IntegrableOn, Measure.restrict_pi_pi] at hIoc
  simpa [IntegrableOn, Set.uIoc_of_le htwoPi] using hIoc

end

end YangMills.RG
