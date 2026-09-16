/- STATIC DRAFT ONLY -- NOT COMPILER-VERIFIED.

Four-coordinate contour telescope for the literal mass-uniform fine-lattice
left derivative.  Every partial-stage integrability fact and every stage
transition is constructed internally. -/

import YangMills.RG.BalabanCMP89Eq251StabilizedEndpointProductIntegrability
import YangMills.RG.BalabanCMP89Eq249FineLatticeLeftDerivativeOneCoordinateContourShift

namespace YangMills.RG

open MeasureTheory

noncomputable section

/-- Literal left derivative at one partial signed-contour stage. -/
def cmp89Eq249FineLatticeLeftDerivativePartialProductIntegrand_draft
    (L j : ℕ) [NeZero L] (mass a rho : ℝ) (stage : ℕ) (mu : Fin 4)
    (endpointU : Fin 4 → ℤ) (x : Fin 4 → ℝ) : ℂ :=
  let endpointDisplacement :=
    cmp89Eq249PhysicalFineLatticeDisplacement
      (((L ^ j : ℕ) : ℝ)⁻¹) endpointU
  cmp89Eq249FineLatticeStabilizedFourierLeftDerivativeKernelIntegrand
    L j mass a
    (cmp89Eq251EndpointPartialSignedContourMomentum stage rho x
      endpointDisplacement)
    mu endpointU

/-- Every partial derivative stage is product-integrable, derived from the
mass-uniform D1 holomorphy on the compact Brillouin cube. -/
theorem integrable_cmp89Eq249FineLatticeLeftDerivativePartialProductIntegrand_draft
    {L j : ℕ} [NeZero L] {mass a rho : ℝ}
    (ha : 0 ≤ a) (hrho : 0 ≤ rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hwindow : CMP89Eq249CentralStabilizedComplexWindow a rho)
    (hmass : CMP89Eq251UniformMassWindow mass)
    (stage : ℕ) (mu : Fin 4) (endpointU : Fin 4 → ℤ) :
    Integrable
      (cmp89Eq249FineLatticeLeftDerivativePartialProductIntegrand_draft
        L j mass a rho stage mu endpointU)
      (Measure.pi fun _ : Fin 4 =>
        volume.restrict (Set.uIoc 0 (2 * Real.pi))) := by
  have htwoPi : (0 : ℝ) ≤ 2 * Real.pi :=
    mul_nonneg (by norm_num) Real.pi_pos.le
  let endpointDisplacement : Fin 4 → ℝ :=
    cmp89Eq249PhysicalFineLatticeDisplacement
      (((L ^ j : ℕ) : ℝ)⁻¹) endpointU
  have hcont : ContinuousOn (fun x : Fin 4 → ℝ =>
      cmp89Eq249FineLatticeStabilizedFourierLeftDerivativeKernelIntegrand
        L j mass a
        (cmp89Eq251EndpointPartialSignedContourMomentum
          stage rho x endpointDisplacement)
        mu endpointU)
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
      differentiableAt_cmp89Eq249FineLatticeStabilizedFourierLeftDerivativeKernelIntegrand_massUniform_draft
        (L := L) (j := j) (mass := mass) (a := a) (rho := rho)
        ha hrho hamplitude hradius hwindow hmass hp
        (cmp89Eq251EndpointPartialSignedContourMomentum_re
          stage rho x endpointDisplacement)
        (abs_im_cmp89Eq251EndpointPartialSignedContourMomentum_le
          hrho stage x endpointDisplacement)
        mu endpointU
    have hinner : ContinuousAt (fun y : Fin 4 → ℝ =>
        cmp89Eq251EndpointPartialSignedContourMomentum
          stage rho y endpointDisplacement) x :=
      (continuous_cmp89Eq251EndpointPartialSignedContourMomentum
        stage rho endpointDisplacement).continuousAt
    exact (houter.continuousAt.comp hinner).continuousWithinAt
  have hIcc : IntegrableOn (fun x : Fin 4 → ℝ =>
      cmp89Eq249FineLatticeStabilizedFourierLeftDerivativeKernelIntegrand
        L j mass a
        (cmp89Eq251EndpointPartialSignedContourMomentum
          stage rho x endpointDisplacement)
        mu endpointU)
      (Set.Icc (fun _ : Fin 4 => 0) (fun _ => 2 * Real.pi))
      (volume : Measure (Fin 4 → ℝ)) :=
    hcont.integrableOn_compact
      (isCompact_Icc : IsCompact
        (Set.Icc (fun _ : Fin 4 => 0) (fun _ => 2 * Real.pi)))
  have hIoc : IntegrableOn (fun x : Fin 4 → ℝ =>
      cmp89Eq249FineLatticeStabilizedFourierLeftDerivativeKernelIntegrand
        L j mass a
        (cmp89Eq251EndpointPartialSignedContourMomentum
          stage rho x endpointDisplacement)
        mu endpointU)
      (Set.univ.pi fun _ : Fin 4 => Set.Ioc 0 (2 * Real.pi))
      (volume : Measure (Fin 4 → ℝ)) :=
    hIcc.congr_set_ae Measure.univ_pi_Ioc_ae_eq_Icc
  rw [IntegrableOn, volume_pi, Measure.restrict_pi_pi] at hIoc
  simpa [cmp89Eq249FineLatticeLeftDerivativePartialProductIntegrand_draft,
    endpointDisplacement, IntegrableOn,
    Set.uIoc_of_le htwoPi] using hIoc

/-- Shift one coordinate of the derivative product integral from partial
stage `r` to `r+1`. -/
theorem integral_cmp89Eq249FineLatticeLeftDerivativePartialProductIntegrand_stage_succ_draft
    {L j : ℕ} [NeZero L] {mass a rho : ℝ}
    (ha : 0 ≤ a) (hrho : 0 ≤ rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hwindow : CMP89Eq249CentralStabilizedComplexWindow a rho)
    (hmass : CMP89Eq251UniformMassWindow mass)
    (stage : ℕ) (nu : Fin 4) (hstage : stage = nu.val)
    (mu : Fin 4) (endpointU : Fin 4 → ℤ) :
    (∫ x, cmp89Eq249FineLatticeLeftDerivativePartialProductIntegrand_draft
        L j mass a rho stage mu endpointU x
      ∂(Measure.pi fun _ : Fin 4 =>
        volume.restrict (Set.uIoc 0 (2 * Real.pi)))) =
      ∫ x, cmp89Eq249FineLatticeLeftDerivativePartialProductIntegrand_draft
        L j mass a rho (stage + 1) mu endpointU x
      ∂(Measure.pi fun _ : Fin 4 =>
        volume.restrict (Set.uIoc 0 (2 * Real.pi))) := by
  let endpointDisplacement : Fin 4 → ℝ :=
    cmp89Eq249PhysicalFineLatticeDisplacement
      (((L ^ j : ℕ) : ℝ)⁻¹) endpointU
  have htwoPi : (0 : ℝ) ≤ 2 * Real.pi :=
    mul_nonneg (by norm_num) Real.pi_pos.le
  have hf :=
    integrable_cmp89Eq249FineLatticeLeftDerivativePartialProductIntegrand_draft
      (L := L) (j := j) (mass := mass) (a := a) (rho := rho)
      ha hrho hamplitude hradius hwindow hmass stage mu endpointU
  have hg :=
    integrable_cmp89Eq249FineLatticeLeftDerivativePartialProductIntegrand_draft
      (L := L) (j := j) (mass := mass) (a := a) (rho := rho)
      ha hrho hamplitude hradius hwindow hmass (stage + 1) mu endpointU
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
    intervalIntegral_cmp89Eq249FineLatticeStabilizedFourierLeftDerivativeKernelIntegrand_coordinateShift_massUniform_draft
      (L := L) (j := j) (mass := mass) (a := a) (rho := rho)
      (eta := eta) ha hrho hamplitude hradius hwindow hmass
      heta nu hp hface hreal himag hnuImag mu endpointU
  simpa [cmp89Eq249FineLatticeLeftDerivativePartialProductIntegrand_draft,
    endpointDisplacement, z, eta,
    cmp89Eq251PhysicalCoordinateLine_partialSigned_eq stage rho nu hstage,
    cmp89Eq251PhysicalCoordinateLine_partialSigned_add_eta_eq
      stage rho nu hstage] using hshift

/-- The four coordinate shifts telescope exactly for the derivative. -/
theorem integral_cmp89Eq249FineLatticeLeftDerivativePartialProductIntegrand_zero_eq_four_draft
    {L j : ℕ} [NeZero L] {mass a rho : ℝ}
    (ha : 0 ≤ a) (hrho : 0 ≤ rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hwindow : CMP89Eq249CentralStabilizedComplexWindow a rho)
    (hmass : CMP89Eq251UniformMassWindow mass)
    (mu : Fin 4) (endpointU : Fin 4 → ℤ) :
    (∫ x, cmp89Eq249FineLatticeLeftDerivativePartialProductIntegrand_draft
        L j mass a rho 0 mu endpointU x
      ∂(Measure.pi fun _ : Fin 4 =>
        volume.restrict (Set.uIoc 0 (2 * Real.pi)))) =
      ∫ x, cmp89Eq249FineLatticeLeftDerivativePartialProductIntegrand_draft
        L j mass a rho 4 mu endpointU x
      ∂(Measure.pi fun _ : Fin 4 =>
        volume.restrict (Set.uIoc 0 (2 * Real.pi))) := by
  have h0 :=
    integral_cmp89Eq249FineLatticeLeftDerivativePartialProductIntegrand_stage_succ_draft
      (L := L) (j := j) (mass := mass) (a := a) (rho := rho)
      ha hrho hamplitude hradius hwindow hmass
      (stage := 0) (nu := (0 : Fin 4)) (hstage := by norm_num) mu endpointU
  have h1 :=
    integral_cmp89Eq249FineLatticeLeftDerivativePartialProductIntegrand_stage_succ_draft
      (L := L) (j := j) (mass := mass) (a := a) (rho := rho)
      ha hrho hamplitude hradius hwindow hmass
      (stage := 1) (nu := (1 : Fin 4)) (hstage := by norm_num) mu endpointU
  have h2 :=
    integral_cmp89Eq249FineLatticeLeftDerivativePartialProductIntegrand_stage_succ_draft
      (L := L) (j := j) (mass := mass) (a := a) (rho := rho)
      ha hrho hamplitude hradius hwindow hmass
      (stage := 2) (nu := (2 : Fin 4)) (hstage := by norm_num) mu endpointU
  have h3 :=
    integral_cmp89Eq249FineLatticeLeftDerivativePartialProductIntegrand_stage_succ_draft
      (L := L) (j := j) (mass := mass) (a := a) (rho := rho)
      ha hrho hamplitude hradius hwindow hmass
      (stage := 3) (nu := (3 : Fin 4)) (hstage := by norm_num) mu endpointU
  exact h0.trans (h1.trans (h2.trans h3))

/-- The real derivative product integral equals its fully signed contour
integral, with no strictly-positive-mass premise. -/
theorem integral_cmp89Eq249FineLatticeStabilizedFourierLeftDerivativeKernelIntegrand_eq_signed_massUniform_draft
    {L j : ℕ} [NeZero L] {mass a rho : ℝ}
    (ha : 0 ≤ a) (hrho : 0 ≤ rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hwindow : CMP89Eq249CentralStabilizedComplexWindow a rho)
    (hmass : CMP89Eq251UniformMassWindow mass)
    (mu : Fin 4) (endpointU : Fin 4 → ℤ) :
    (∫ x,
      cmp89Eq249FineLatticeStabilizedFourierLeftDerivativeKernelIntegrand
        L j mass a
        (fun nu => (cmp89Eq251PhysicalBrillouinParameter x nu : ℂ))
        mu endpointU
      ∂(Measure.pi fun _ : Fin 4 =>
        volume.restrict (Set.uIoc 0 (2 * Real.pi)))) =
      ∫ x,
        cmp89Eq249FineLatticeStabilizedFourierLeftDerivativeKernelIntegrand
          L j mass a
          (cmp89Eq251SignedContourMomentum rho
            (cmp89Eq251PhysicalBrillouinParameter x)
            (cmp89Eq249PhysicalFineLatticeDisplacement
              (((L ^ j : ℕ) : ℝ)⁻¹) endpointU))
          mu endpointU
      ∂(Measure.pi fun _ : Fin 4 =>
        volume.restrict (Set.uIoc 0 (2 * Real.pi))) := by
  have h :=
    integral_cmp89Eq249FineLatticeLeftDerivativePartialProductIntegrand_zero_eq_four_draft
      (L := L) (j := j) (mass := mass) (a := a) (rho := rho)
      ha hrho hamplitude hradius hwindow hmass mu endpointU
  simpa [cmp89Eq249FineLatticeLeftDerivativePartialProductIntegrand_draft,
    cmp89Eq251EndpointPartialSignedContourMomentum_zero,
    cmp89Eq251EndpointPartialSignedContourMomentum_four] using h

end

end YangMills.RG
