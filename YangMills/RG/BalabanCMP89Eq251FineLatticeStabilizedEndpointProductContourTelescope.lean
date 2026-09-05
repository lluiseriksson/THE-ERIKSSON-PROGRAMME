/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP89Eq251FineLatticeStabilizedEndpointOneCoordinateContourShift
import YangMills.RG.BalabanCMP89Eq251StabilizedEndpointProductIntegrability
import YangMills.RG.BalabanCMP89Eq251StabilizedEndpointProductCoordinateShift

/-!
# Cold-sealed four-coordinate telescope for a fine-lattice endpoint

The existing partial signed momentum and compact-product integrability are
genuinely generic in a real endpoint displacement.  This module specializes
them to `u/(L^j)` at `alpha = 0`, proves the literal product-integral
transition `stage -> stage+1` from the sealed fine-lattice one-coordinate
shift, and composes the four coordinates of `Fin 4`.

No family of endpoint functions, slice equality, integrability certificate or
complete contour equality is accepted as input.  This treats one endpoint
only; normalized integration, two-endpoint recombination, physical `B0`,
window-15 attainment and terminal fields remain open.
-/

namespace YangMills.RG

open MeasureTheory

noncomputable section

/-- One fine-lattice stabilized endpoint at a partial signed contour stage. -/
def cmp89Eq251FineLatticeStabilizedEndpointPartialProductIntegrand
    (L j : ℕ) (mass a rho : ℝ) (stage : ℕ) (mu : Fin 4)
    (holderDisplacement : Fin 4 → ℝ) (endpointU : Fin 4 → ℤ)
    (x : Fin 4 → ℝ) : ℂ :=
  let endpointDisplacement :=
    cmp89Eq249PhysicalFineLatticeDisplacement
      (((L ^ j : ℕ) : ℝ)⁻¹) endpointU
  cmp89Eq251ComplexStabilizedEndpointIntegrand 4 L j mass a 0
    (cmp89Eq251EndpointPartialSignedContourMomentum stage rho x
      endpointDisplacement)
    mu holderDisplacement endpointDisplacement

/-- Every fine-lattice partial stage is product-integrable.  This is produced
by the sealed generic common-strip theorem, not accepted as a certificate. -/
theorem integrable_cmp89Eq251FineLatticeStabilizedEndpointPartialProductIntegrand
    {L j : ℕ} [NeZero L] {mass a rho : ℝ}
    (ha : 0 ≤ a) (hmassPos : 0 < mass) (hrho : 0 ≤ rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hwindow : CMP89Eq249CentralStabilizedComplexWindow a rho)
    (hmass : CMP89Eq251UniformMassWindow mass)
    (stage : ℕ) (mu : Fin 4) (holderDisplacement : Fin 4 → ℝ)
    (endpointU : Fin 4 → ℤ) :
    Integrable
      (cmp89Eq251FineLatticeStabilizedEndpointPartialProductIntegrand
        L j mass a rho stage mu holderDisplacement endpointU)
      (Measure.pi fun _ : Fin 4 =>
        volume.restrict (Set.uIoc 0 (2 * Real.pi))) := by
  exact
    integrable_cmp89Eq251ComplexStabilizedEndpointIntegrand_partialSigned
      (L := L) (j := j) (mass := mass) (a := a) (alpha := 0)
      (rho := rho) ha hmassPos hrho hamplitude hradius hwindow hmass
      stage mu holderDisplacement
      (cmp89Eq249PhysicalFineLatticeDisplacement
        (((L ^ j : ℕ) : ℝ)⁻¹) endpointU)

/-- Shift one coordinate of the literal fine-lattice endpoint product
integral from partial stage `r` to stage `r+1`. -/
theorem integral_cmp89Eq251FineLatticeStabilizedEndpointPartialProductIntegrand_stage_succ
    {L j : ℕ} [NeZero L] {mass a rho : ℝ}
    (ha : 0 ≤ a) (hmassPos : 0 < mass) (hrho : 0 ≤ rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hwindow : CMP89Eq249CentralStabilizedComplexWindow a rho)
    (hmass : CMP89Eq251UniformMassWindow mass)
    (stage : ℕ) (nu mu : Fin 4) (hstage : stage = nu.val)
    (holderDisplacement : Fin 4 → ℝ) (endpointU : Fin 4 → ℤ) :
    (∫ x, cmp89Eq251FineLatticeStabilizedEndpointPartialProductIntegrand
        L j mass a rho stage mu holderDisplacement endpointU x
      ∂(Measure.pi fun _ : Fin 4 =>
        volume.restrict (Set.uIoc 0 (2 * Real.pi)))) =
      ∫ x, cmp89Eq251FineLatticeStabilizedEndpointPartialProductIntegrand
        L j mass a rho (stage + 1) mu holderDisplacement endpointU x
      ∂(Measure.pi fun _ : Fin 4 =>
        volume.restrict (Set.uIoc 0 (2 * Real.pi))) := by
  let endpointDisplacement : Fin 4 → ℝ :=
    cmp89Eq249PhysicalFineLatticeDisplacement
      (((L ^ j : ℕ) : ℝ)⁻¹) endpointU
  have htwoPi : (0 : ℝ) ≤ 2 * Real.pi :=
    mul_nonneg (by norm_num) Real.pi_pos.le
  have hf :=
    integrable_cmp89Eq251FineLatticeStabilizedEndpointPartialProductIntegrand
      (L := L) (j := j) (mass := mass) (a := a) (rho := rho)
      ha hmassPos hrho hamplitude hradius hwindow hmass stage mu
        holderDisplacement endpointU
  have hg :=
    integrable_cmp89Eq251FineLatticeStabilizedEndpointPartialProductIntegrand
      (L := L) (j := j) (mass := mass) (a := a) (rho := rho)
      ha hmassPos hrho hamplitude hradius hwindow hmass (stage + 1) mu
        holderDisplacement endpointU
  refine integral_pi_restrict_uIoc_eq_of_coordinate_intervalIntegral_ae_eq
    htwoPi nu hf hg ?_
  have hmem : ∀ᵐ y ∂(Measure.pi fun _ : Fin 3 =>
      volume.restrict (Set.uIoc 0 (2 * Real.pi))),
      y ∈ Set.univ.pi fun _ : Fin 3 => Set.Ioc 0 (2 * Real.pi) := by
    have hset : MeasurableSet
        (Set.univ.pi fun _ : Fin 3 => Set.Ioc (0 : ℝ) (2 * Real.pi)) :=
      MeasurableSet.univ_pi fun _ => measurableSet_Ioc
    have hae := ae_restrict_mem
      (μ := Measure.pi fun _ : Fin 3 => volume) hset
    rw [← Measure.restrict_pi_pi]
    simpa [Set.uIoc_of_le htwoPi] using hae
  filter_upwards [hmem] with y hy
  let p : Fin 4 → ℝ :=
    cmp89Eq251PhysicalBrillouinParameter (nu.insertNth 0 y)
  let z : Fin 4 → ℂ :=
    cmp89Eq251EndpointPartialSignedContourMomentum stage rho
      (nu.insertNth 0 y) endpointDisplacement
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
      stage rho (nu.insertNth 0 y) endpointDisplacement k
  have himag : ∀ k, |(z k).im| ≤ rho := by
    intro k
    exact abs_im_cmp89Eq251EndpointPartialSignedContourMomentum_le
      hrho stage (nu.insertNth 0 y) endpointDisplacement k
  have hnuImag : (z nu).im = 0 := by
    simp [z, cmp89Eq251EndpointPartialSignedContourMomentum_im, hstage]
  let eta : ℝ :=
    rho * (SignType.sign (endpointDisplacement nu) : ℝ)
  have heta : |eta| ≤ rho := by
    have h := abs_im_cmp89Eq251SignedContourMomentum_le hrho p
      endpointDisplacement nu
    simpa [eta, cmp89Eq251SignedContourMomentum_im] using h
  have hshift :=
    intervalIntegral_cmp89Eq251ComplexStabilizedEndpointIntegrand_zero_physicalFine_coordinateShift
      (L := L) (j := j) (mass := mass) (a := a) (rho := rho)
      (eta := eta) ha hmassPos hrho hamplitude hradius hwindow hmass
      heta nu mu hp hface hreal himag hnuImag holderDisplacement endpointU
  simpa [cmp89Eq251FineLatticeStabilizedEndpointPartialProductIntegrand,
    endpointDisplacement, z, eta,
    cmp89Eq251PhysicalCoordinateLine_partialSigned_eq stage rho nu hstage,
    cmp89Eq251PhysicalCoordinateLine_partialSigned_add_eta_eq
      stage rho nu hstage] using hshift

/-- The four literal coordinate transitions telescope from the real product
integral to the fully signed fine-lattice endpoint integral. -/
theorem integral_cmp89Eq251FineLatticeStabilizedEndpointPartialProductIntegrand_zero_eq_four
    {L j : ℕ} [NeZero L] {mass a rho : ℝ}
    (ha : 0 ≤ a) (hmassPos : 0 < mass) (hrho : 0 ≤ rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hwindow : CMP89Eq249CentralStabilizedComplexWindow a rho)
    (hmass : CMP89Eq251UniformMassWindow mass)
    (mu : Fin 4) (holderDisplacement : Fin 4 → ℝ)
    (endpointU : Fin 4 → ℤ) :
    (∫ x, cmp89Eq251FineLatticeStabilizedEndpointPartialProductIntegrand
        L j mass a rho 0 mu holderDisplacement endpointU x
      ∂(Measure.pi fun _ : Fin 4 =>
        volume.restrict (Set.uIoc 0 (2 * Real.pi)))) =
      ∫ x, cmp89Eq251FineLatticeStabilizedEndpointPartialProductIntegrand
        L j mass a rho 4 mu holderDisplacement endpointU x
      ∂(Measure.pi fun _ : Fin 4 =>
        volume.restrict (Set.uIoc 0 (2 * Real.pi))) := by
  have h0 :=
    integral_cmp89Eq251FineLatticeStabilizedEndpointPartialProductIntegrand_stage_succ
      (L := L) (j := j) (mass := mass) (a := a) (rho := rho)
      ha hmassPos hrho hamplitude hradius hwindow hmass
      (stage := 0) (nu := (0 : Fin 4)) (mu := mu) (hstage := by norm_num)
      (holderDisplacement := holderDisplacement) (endpointU := endpointU)
  have h1 :=
    integral_cmp89Eq251FineLatticeStabilizedEndpointPartialProductIntegrand_stage_succ
      (L := L) (j := j) (mass := mass) (a := a) (rho := rho)
      ha hmassPos hrho hamplitude hradius hwindow hmass
      (stage := 1) (nu := (1 : Fin 4)) (mu := mu) (hstage := by norm_num)
      (holderDisplacement := holderDisplacement) (endpointU := endpointU)
  have h2 :=
    integral_cmp89Eq251FineLatticeStabilizedEndpointPartialProductIntegrand_stage_succ
      (L := L) (j := j) (mass := mass) (a := a) (rho := rho)
      ha hmassPos hrho hamplitude hradius hwindow hmass
      (stage := 2) (nu := (2 : Fin 4)) (mu := mu) (hstage := by norm_num)
      (holderDisplacement := holderDisplacement) (endpointU := endpointU)
  have h3 :=
    integral_cmp89Eq251FineLatticeStabilizedEndpointPartialProductIntegrand_stage_succ
      (L := L) (j := j) (mass := mass) (a := a) (rho := rho)
      ha hmassPos hrho hamplitude hradius hwindow hmass
      (stage := 3) (nu := (3 : Fin 4)) (mu := mu) (hstage := by norm_num)
      (holderDisplacement := holderDisplacement) (endpointU := endpointU)
  exact h0.trans (h1.trans (h2.trans h3))

/-- One fine-lattice stabilized endpoint product integral equals its own fully
signed contour integral.  No sign shared with a second endpoint is imposed. -/
theorem integral_cmp89Eq251ComplexStabilizedEndpointIntegrand_zero_physicalFine_eq_signed
    {L j : ℕ} [NeZero L] {mass a rho : ℝ}
    (ha : 0 ≤ a) (hmassPos : 0 < mass) (hrho : 0 ≤ rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hwindow : CMP89Eq249CentralStabilizedComplexWindow a rho)
    (hmass : CMP89Eq251UniformMassWindow mass)
    (mu : Fin 4) (holderDisplacement : Fin 4 → ℝ)
    (endpointU : Fin 4 → ℤ) :
    (∫ x, cmp89Eq251ComplexStabilizedEndpointIntegrand 4 L j mass a 0
        (fun nu => (cmp89Eq251PhysicalBrillouinParameter x nu : ℂ)) mu
        holderDisplacement
        (cmp89Eq249PhysicalFineLatticeDisplacement
          (((L ^ j : ℕ) : ℝ)⁻¹) endpointU)
      ∂(Measure.pi fun _ : Fin 4 =>
        volume.restrict (Set.uIoc 0 (2 * Real.pi)))) =
      ∫ x, cmp89Eq251ComplexStabilizedEndpointIntegrand 4 L j mass a 0
        (cmp89Eq251SignedContourMomentum rho
          (cmp89Eq251PhysicalBrillouinParameter x)
          (cmp89Eq249PhysicalFineLatticeDisplacement
            (((L ^ j : ℕ) : ℝ)⁻¹) endpointU)) mu
        holderDisplacement
        (cmp89Eq249PhysicalFineLatticeDisplacement
          (((L ^ j : ℕ) : ℝ)⁻¹) endpointU)
      ∂(Measure.pi fun _ : Fin 4 =>
        volume.restrict (Set.uIoc 0 (2 * Real.pi))) := by
  have h :=
    integral_cmp89Eq251FineLatticeStabilizedEndpointPartialProductIntegrand_zero_eq_four
      (L := L) (j := j) (mass := mass) (a := a) (rho := rho)
      ha hmassPos hrho hamplitude hradius hwindow hmass mu
      holderDisplacement endpointU
  simpa [cmp89Eq251FineLatticeStabilizedEndpointPartialProductIntegrand]
    using h

end

end YangMills.RG
