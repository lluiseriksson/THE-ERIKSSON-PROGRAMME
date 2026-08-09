/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP89Eq251StabilizedEndpointProductIntegrability
import YangMills.RG.IntervalIntegralPiCoordinateTransport

/-!
# PRE-VALIDATION: one-coordinate transport of the stabilized endpoint product integral

The source in this module is present, but its `.olean` has not yet been
materialized and its result has not yet been verified by the Lean compiler.

This module specializes the sealed product-measure transport to one literal
partial signed endpoint integrand.  The real cube is split at one coordinate,
the one-dimensional endpoint contour theorem shifts exactly that coordinate,
and the remaining three coordinates are reassembled by the exact finite-Pi
measure equivalence.

No family of endpoint functions, slice equality, integrability certificate,
four-coordinate iteration, complete contour equality, bound `B0`, owner
dictionary or window-15 conclusion is accepted.
-/

namespace YangMills.RG

open MeasureTheory

noncomputable section

/-- The physical stabilized endpoint integrand at one partial signed stage. -/
def cmp89Eq251StabilizedEndpointPartialProductIntegrand
    (L j : ℕ) (mass a alpha rho : ℝ) (stage : ℕ) (mu : Fin 4)
    (holderU endpointU : Fin 4 → ℤ) (x : Fin 4 → ℝ) : ℂ :=
  cmp89Eq251ComplexStabilizedEndpointIntegrand 4 L j mass a alpha
    (cmp89Eq251EndpointPartialSignedContourMomentum stage rho x
      (cmp89Eq251LatticeDisplacement endpointU))
    mu (cmp89Eq251LatticeDisplacement holderU)
    (cmp89Eq251LatticeDisplacement endpointU)

/-- Every literal partial-stage endpoint integrand has the product
integrability needed by coordinate transport. -/
theorem integrable_cmp89Eq251StabilizedEndpointPartialProductIntegrand
    {L j : ℕ} [NeZero L] {mass a alpha rho : ℝ}
    (ha : 0 ≤ a) (hmassPos : 0 < mass) (hrho : 0 ≤ rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hwindow : CMP89Eq249CentralStabilizedComplexWindow a rho)
    (hmass : CMP89Eq251UniformMassWindow mass)
    (stage : ℕ) (mu : Fin 4) (holderU endpointU : Fin 4 → ℤ) :
    Integrable
      (cmp89Eq251StabilizedEndpointPartialProductIntegrand
        L j mass a alpha rho stage mu holderU endpointU)
      (Measure.pi fun _ : Fin 4 =>
        volume.restrict (Set.uIoc 0 (2 * Real.pi))) := by
  exact
    integrable_cmp89Eq251ComplexStabilizedEndpointIntegrand_partialSigned
      (L := L) (j := j) (mass := mass) (a := a) (alpha := alpha)
      (rho := rho)
      ha hmassPos hrho hamplitude hradius hwindow hmass stage mu
      (cmp89Eq251LatticeDisplacement holderU)
      (cmp89Eq251LatticeDisplacement endpointU)

/-- Replacing coordinate `nu` in the real cube is exactly the unshifted
coordinate line through the lower face of partial stage `nu.val`. -/
theorem cmp89Eq251PhysicalCoordinateLine_partialSigned_eq
    (stage : ℕ) (rho : ℝ) (nu : Fin 4) (hstage : stage = nu.val)
    (x : ℝ) (y : Fin 3 → ℝ) (endpointDisplacement : Fin 4 → ℝ) :
    cmp89Eq251PhysicalCoordinateLine nu
        (cmp89Eq251EndpointPartialSignedContourMomentum stage rho
          (nu.insertNth 0 y) endpointDisplacement)
        (x : ℂ) =
      cmp89Eq251EndpointPartialSignedContourMomentum stage rho
        (nu.insertNth x y) endpointDisplacement := by
  funext k
  by_cases hk : k = nu
  · subst k
    simp [cmp89Eq251PhysicalCoordinateLine,
      cmp89Eq251EndpointPartialSignedContourMomentum,
      cmp89Eq251PhysicalBrillouinParameter, hstage, Pi.single_apply]
  · obtain ⟨i, rfl⟩ := Fin.exists_succAbove_eq hk
    simp [cmp89Eq251PhysicalCoordinateLine,
      cmp89Eq251EndpointPartialSignedContourMomentum,
      cmp89Eq251PhysicalBrillouinParameter, Pi.single_apply]

/-- Adding the signed imaginary displacement to coordinate `nu` turns stage
`nu.val` into stage `nu.val + 1`, with every other coordinate unchanged. -/
theorem cmp89Eq251PhysicalCoordinateLine_partialSigned_add_eta_eq
    (stage : ℕ) (rho : ℝ) (nu : Fin 4) (hstage : stage = nu.val)
    (x : ℝ) (y : Fin 3 → ℝ) (endpointDisplacement : Fin 4 → ℝ) :
    cmp89Eq251PhysicalCoordinateLine nu
        (cmp89Eq251EndpointPartialSignedContourMomentum stage rho
          (nu.insertNth 0 y) endpointDisplacement)
        ((x : ℂ) +
          (rho * (SignType.sign (endpointDisplacement nu) : ℝ)) * Complex.I) =
      cmp89Eq251EndpointPartialSignedContourMomentum (stage + 1) rho
        (nu.insertNth x y) endpointDisplacement := by
  funext k
  by_cases hk : k = nu
  · subst k
    simp [cmp89Eq251PhysicalCoordinateLine,
      cmp89Eq251EndpointPartialSignedContourMomentum,
      cmp89Eq251SignedContourMomentum,
      cmp89Eq251PhysicalBrillouinParameter, hstage, Pi.single_apply]
    ring
  · obtain ⟨i, rfl⟩ := Fin.exists_succAbove_eq hk
    have hlt : (nu.succAbove i).val < stage + 1 ↔
        (nu.succAbove i).val < stage := by
      omega
    simp [cmp89Eq251PhysicalCoordinateLine,
      cmp89Eq251EndpointPartialSignedContourMomentum,
      cmp89Eq251PhysicalBrillouinParameter, Pi.single_apply, hlt]

/-- Shift one coordinate of the literal four-dimensional endpoint product
integral from partial stage `r` to stage `r+1`. -/
theorem integral_cmp89Eq251StabilizedEndpointPartialProductIntegrand_stage_succ
    {L j : ℕ} [NeZero L] {mass a alpha rho : ℝ}
    (ha : 0 ≤ a) (hmassPos : 0 < mass) (hrho : 0 ≤ rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hwindow : CMP89Eq249CentralStabilizedComplexWindow a rho)
    (hmass : CMP89Eq251UniformMassWindow mass)
    (stage : ℕ) (nu mu : Fin 4) (hstage : stage = nu.val)
    (holderU endpointU : Fin 4 → ℤ) :
    (∫ x, cmp89Eq251StabilizedEndpointPartialProductIntegrand
        L j mass a alpha rho stage mu holderU endpointU x
      ∂(Measure.pi fun _ : Fin 4 =>
        volume.restrict (Set.uIoc 0 (2 * Real.pi)))) =
      ∫ x, cmp89Eq251StabilizedEndpointPartialProductIntegrand
        L j mass a alpha rho (stage + 1) mu holderU endpointU x
      ∂(Measure.pi fun _ : Fin 4 =>
        volume.restrict (Set.uIoc 0 (2 * Real.pi))) := by
  have htwoPi : (0 : ℝ) ≤ 2 * Real.pi :=
    mul_nonneg (by norm_num) Real.pi_pos.le
  have hf :=
    integrable_cmp89Eq251StabilizedEndpointPartialProductIntegrand
      (L := L) (j := j) (mass := mass) (a := a) (alpha := alpha)
      (rho := rho)
      ha hmassPos hrho hamplitude hradius hwindow hmass stage mu
        holderU endpointU
  have hg :=
    integrable_cmp89Eq251StabilizedEndpointPartialProductIntegrand
      (L := L) (j := j) (mass := mass) (a := a) (alpha := alpha)
      (rho := rho)
      ha hmassPos hrho hamplitude hradius hwindow hmass (stage + 1) mu
        holderU endpointU
  refine integral_pi_restrict_uIoc_eq_of_coordinate_intervalIntegral_ae_eq
    htwoPi nu hf hg ?_
  have hmem : ∀ᵐ y ∂(Measure.pi fun _ : Fin 3 =>
      volume.restrict (Set.uIoc 0 (2 * Real.pi))),
      y ∈ Set.univ.pi fun _ : Fin 3 => Set.Ioc 0 (2 * Real.pi) := by
    have hset : MeasurableSet
        (Set.univ.pi fun _ : Fin 3 => Set.Ioc (0 : ℝ) (2 * Real.pi)) :=
      MeasurableSet.univ_pi fun _ => measurableSet_Ioc
    rw [← Measure.restrict_pi_pi]
    exact ae_restrict_mem hset
  filter_upwards [hmem] with y hy
  let p : Fin 4 → ℝ :=
    cmp89Eq251PhysicalBrillouinParameter (nu.insertNth 0 y)
  let z : Fin 4 → ℂ :=
    cmp89Eq251EndpointPartialSignedContourMomentum stage rho
      (nu.insertNth 0 y) (cmp89Eq251LatticeDisplacement endpointU)
  have hp : ∀ k, |p k| ≤ Real.pi := by
    intro k
    by_cases hk : k = nu
    · subst k
      simp [p, cmp89Eq251PhysicalBrillouinParameter,
        abs_of_pos Real.pi_pos]
    · obtain ⟨i, rfl⟩ := Fin.exists_succAbove_eq hk
      have hyi := hy i (Set.mem_univ i)
      rw [abs_le]
      simp only [p, cmp89Eq251PhysicalBrillouinParameter,
        Fin.insertNth_apply_succAbove]
      constructor <;> linarith [hyi.1, hyi.2, Real.pi_pos]
  have hface : p nu = -Real.pi := by
    simp [p, cmp89Eq251PhysicalBrillouinParameter]
  have hreal : ∀ k, (z k).re = p k := by
    intro k
    exact cmp89Eq251EndpointPartialSignedContourMomentum_re
      stage rho (nu.insertNth 0 y)
        (cmp89Eq251LatticeDisplacement endpointU) k
  have himag : ∀ k, |(z k).im| ≤ rho := by
    intro k
    exact abs_im_cmp89Eq251EndpointPartialSignedContourMomentum_le
      hrho stage (nu.insertNth 0 y)
        (cmp89Eq251LatticeDisplacement endpointU) k
  have hnuImag : (z nu).im = 0 := by
    simp [z, cmp89Eq251EndpointPartialSignedContourMomentum_im, hstage]
  let eta : ℝ :=
    rho * (SignType.sign
      (cmp89Eq251LatticeDisplacement endpointU nu) : ℝ)
  have heta : |eta| ≤ rho := by
    have h := abs_im_cmp89Eq251SignedContourMomentum_le hrho p
      (cmp89Eq251LatticeDisplacement endpointU) nu
    simpa [eta, cmp89Eq251SignedContourMomentum_im] using h
  have hshift :=
    intervalIntegral_cmp89Eq251ComplexStabilizedEndpointIntegrand_coordinateShift
      (L := L) (j := j) (mass := mass) (a := a) (alpha := alpha)
      (rho := rho) (eta := eta)
      ha hmassPos hrho hamplitude hradius hwindow hmass heta nu mu hp
      hface hreal himag hnuImag holderU endpointU
  simpa [cmp89Eq251StabilizedEndpointPartialProductIntegrand, z, eta,
    cmp89Eq251PhysicalCoordinateLine_partialSigned_eq stage rho nu hstage,
    cmp89Eq251PhysicalCoordinateLine_partialSigned_add_eta_eq
      stage rho nu hstage] using hshift

end

end YangMills.RG
