/- STATIC DRAFT ONLY -- NOT COMPILER-VERIFIED.

Four-coordinate product telescope for the complete physical fine-lattice
Holder integrand under the mass-uniform common window.  The Holder numerator
is never split into two endpoint estimates; the contour sign is chosen only
from the transport displacement.  No normalized bound, owner dictionary,
regional B0, window-15 claim or terminal field is asserted here.
-/

import YangMills.RG.BalabanCMP89Eq251StabilizedEndpointProductIntegrability
import YangMills.RG.BalabanCMP89Eq251CompleteHolderMassUniformOneCoordinateContourShift

namespace YangMills.RG

open MeasureTheory

noncomputable section

/-- Complete Holder integrand at one partial signed-contour product stage. -/
def cmp89Eq249CompleteHolderMassUniformPartialProductIntegrand_draft
    (L j : ℕ) [NeZero L] (mass a alpha rho : ℝ) (stage : ℕ)
    (mu : Fin 4) (holderU transportU : Fin 4 → ℤ)
    (x : Fin 4 → ℝ) : ℂ :=
  let xi := cmp89Eq249FineLatticeSpacing L j
  let holderDisplacement :=
    cmp89Eq249PhysicalFineLatticeDisplacement xi holderU
  let transportDisplacement :=
    cmp89Eq249PhysicalFineLatticeDisplacement xi transportU
  cmp89Eq251ComplexStabilizedIntegrand 4 L j mass a alpha
    (cmp89Eq251EndpointPartialSignedContourMomentum stage rho x
      transportDisplacement)
    mu holderDisplacement transportDisplacement

/-- Every partial complete-Holder stage is product-integrable, constructed
from H3a holomorphy on the compact Brillouin cube. -/
theorem
    integrable_cmp89Eq249CompleteHolderMassUniformPartialProductIntegrand_draft
    {L j : ℕ} [NeZero L] {mass a alpha rho : ℝ}
    (ha : 0 ≤ a) (hrho : 0 ≤ rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hwindow : CMP89Eq249CentralStabilizedComplexWindow a rho)
    (hmass : CMP89Eq251UniformMassWindow mass)
    (stage : ℕ) (mu : Fin 4) (holderU transportU : Fin 4 → ℤ) :
    Integrable
      (cmp89Eq249CompleteHolderMassUniformPartialProductIntegrand_draft
        L j mass a alpha rho stage mu holderU transportU)
      (Measure.pi fun _ : Fin 4 =>
        volume.restrict (Set.uIoc 0 (2 * Real.pi))) := by
  have htwoPi : (0 : ℝ) ≤ 2 * Real.pi :=
    mul_nonneg (by norm_num) Real.pi_pos.le
  let xi := cmp89Eq249FineLatticeSpacing L j
  let holderDisplacement : Fin 4 → ℝ :=
    cmp89Eq249PhysicalFineLatticeDisplacement xi holderU
  let transportDisplacement : Fin 4 → ℝ :=
    cmp89Eq249PhysicalFineLatticeDisplacement xi transportU
  have hcont : ContinuousOn (fun x : Fin 4 → ℝ =>
      cmp89Eq251ComplexStabilizedIntegrand 4 L j mass a alpha
        (cmp89Eq251EndpointPartialSignedContourMomentum
          stage rho x transportDisplacement)
        mu holderDisplacement transportDisplacement)
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
      differentiableAt_cmp89Eq251ComplexStabilizedIntegrand_of_commonRadius_massUniform_draft
        (L := L) (j := j) (mass := mass) (a := a) (alpha := alpha)
        (rho := rho) ha hrho hamplitude hradius hwindow hmass hp
        (cmp89Eq251EndpointPartialSignedContourMomentum_re
          stage rho x transportDisplacement)
        (abs_im_cmp89Eq251EndpointPartialSignedContourMomentum_le
          hrho stage x transportDisplacement)
        holderDisplacement transportDisplacement
    have hinner : ContinuousAt (fun y : Fin 4 → ℝ =>
        cmp89Eq251EndpointPartialSignedContourMomentum
          stage rho y transportDisplacement) x :=
      (continuous_cmp89Eq251EndpointPartialSignedContourMomentum
        stage rho transportDisplacement).continuousAt
    exact (houter.continuousAt.comp hinner).continuousWithinAt
  have hIcc : IntegrableOn (fun x : Fin 4 → ℝ =>
      cmp89Eq251ComplexStabilizedIntegrand 4 L j mass a alpha
        (cmp89Eq251EndpointPartialSignedContourMomentum
          stage rho x transportDisplacement)
        mu holderDisplacement transportDisplacement)
      (Set.Icc (fun _ : Fin 4 => 0) (fun _ => 2 * Real.pi))
      (volume : Measure (Fin 4 → ℝ)) :=
    hcont.integrableOn_compact
      (isCompact_Icc : IsCompact
        (Set.Icc (fun _ : Fin 4 => 0) (fun _ => 2 * Real.pi)))
  have hIoc : IntegrableOn (fun x : Fin 4 → ℝ =>
      cmp89Eq251ComplexStabilizedIntegrand 4 L j mass a alpha
        (cmp89Eq251EndpointPartialSignedContourMomentum
          stage rho x transportDisplacement)
        mu holderDisplacement transportDisplacement)
      (Set.univ.pi fun _ : Fin 4 => Set.Ioc 0 (2 * Real.pi))
      (volume : Measure (Fin 4 → ℝ)) :=
    hIcc.congr_set_ae Measure.univ_pi_Ioc_ae_eq_Icc
  rw [IntegrableOn, volume_pi, Measure.restrict_pi_pi] at hIoc
  simpa [cmp89Eq249CompleteHolderMassUniformPartialProductIntegrand_draft,
    xi, holderDisplacement, transportDisplacement, IntegrableOn,
    Set.uIoc_of_le htwoPi] using hIoc

/-- Shift coordinate `nu` from partial stage `nu.val` to the next stage. -/
theorem
    integral_cmp89Eq249CompleteHolderMassUniformPartialProductIntegrand_stage_succ_draft
    {L j : ℕ} [NeZero L] {mass a alpha rho : ℝ}
    (ha : 0 ≤ a) (hrho : 0 ≤ rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hwindow : CMP89Eq249CentralStabilizedComplexWindow a rho)
    (hmass : CMP89Eq251UniformMassWindow mass)
    (stage : ℕ) (nu mu : Fin 4) (hstage : stage = nu.val)
    (holderU transportU : Fin 4 → ℤ) :
    (∫ x, cmp89Eq249CompleteHolderMassUniformPartialProductIntegrand_draft
        L j mass a alpha rho stage mu holderU transportU x
      ∂(Measure.pi fun _ : Fin 4 =>
        volume.restrict (Set.uIoc 0 (2 * Real.pi)))) =
      ∫ x, cmp89Eq249CompleteHolderMassUniformPartialProductIntegrand_draft
        L j mass a alpha rho (stage + 1) mu holderU transportU x
      ∂(Measure.pi fun _ : Fin 4 =>
        volume.restrict (Set.uIoc 0 (2 * Real.pi))) := by
  let xi := cmp89Eq249FineLatticeSpacing L j
  let transportDisplacement : Fin 4 → ℝ :=
    cmp89Eq249PhysicalFineLatticeDisplacement xi transportU
  have htwoPi : (0 : ℝ) ≤ 2 * Real.pi :=
    mul_nonneg (by norm_num) Real.pi_pos.le
  have hf :=
    integrable_cmp89Eq249CompleteHolderMassUniformPartialProductIntegrand_draft
      (L := L) (j := j) (mass := mass) (a := a) (alpha := alpha)
      (rho := rho) ha hrho hamplitude hradius hwindow hmass
      stage mu holderU transportU
  have hg :=
    integrable_cmp89Eq249CompleteHolderMassUniformPartialProductIntegrand_draft
      (L := L) (j := j) (mass := mass) (a := a) (alpha := alpha)
      (rho := rho) ha hrho hamplitude hradius hwindow hmass
      (stage + 1) mu holderU transportU
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
      (nu.insertNth 0 y) transportDisplacement
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
      stage rho (nu.insertNth 0 y) transportDisplacement k
  have himag : ∀ k, |(z k).im| ≤ rho := by
    intro k
    exact abs_im_cmp89Eq251EndpointPartialSignedContourMomentum_le
      hrho stage (nu.insertNth 0 y) transportDisplacement k
  have hnuImag : (z nu).im = 0 := by
    simp [z, cmp89Eq251EndpointPartialSignedContourMomentum_im, hstage]
  let eta : ℝ :=
    rho * (SignType.sign (transportDisplacement nu) : ℝ)
  have heta : |eta| ≤ rho := by
    have h := abs_im_cmp89Eq251SignedContourMomentum_le hrho p
      transportDisplacement nu
    simpa [eta, cmp89Eq251SignedContourMomentum_im] using h
  have hshift :=
    intervalIntegral_cmp89Eq251ComplexStabilizedIntegrand_coordinateShift_massUniform_draft
      (L := L) (j := j) (mass := mass) (a := a) (alpha := alpha)
      (rho := rho) (eta := eta) ha hrho hamplitude hradius hwindow hmass
      heta nu mu hp hface hreal himag hnuImag holderU transportU
  simpa [cmp89Eq249CompleteHolderMassUniformPartialProductIntegrand_draft,
    xi, transportDisplacement, z, eta,
    cmp89Eq251PhysicalCoordinateLine_partialSigned_eq stage rho nu hstage,
    cmp89Eq251PhysicalCoordinateLine_partialSigned_add_eta_eq
      stage rho nu hstage] using hshift

/-- The four coordinate transitions telescope exactly for the complete
fine-lattice Holder integrand. -/
theorem
    integral_cmp89Eq249CompleteHolderMassUniformPartialProductIntegrand_zero_eq_four_draft
    {L j : ℕ} [NeZero L] {mass a alpha rho : ℝ}
    (ha : 0 ≤ a) (hrho : 0 ≤ rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hwindow : CMP89Eq249CentralStabilizedComplexWindow a rho)
    (hmass : CMP89Eq251UniformMassWindow mass)
    (mu : Fin 4) (holderU transportU : Fin 4 → ℤ) :
    (∫ x, cmp89Eq249CompleteHolderMassUniformPartialProductIntegrand_draft
        L j mass a alpha rho 0 mu holderU transportU x
      ∂(Measure.pi fun _ : Fin 4 =>
        volume.restrict (Set.uIoc 0 (2 * Real.pi)))) =
      ∫ x, cmp89Eq249CompleteHolderMassUniformPartialProductIntegrand_draft
        L j mass a alpha rho 4 mu holderU transportU x
      ∂(Measure.pi fun _ : Fin 4 =>
        volume.restrict (Set.uIoc 0 (2 * Real.pi))) := by
  have h0 :=
    integral_cmp89Eq249CompleteHolderMassUniformPartialProductIntegrand_stage_succ_draft
      (L := L) (j := j) (mass := mass) (a := a) (alpha := alpha)
      (rho := rho) ha hrho hamplitude hradius hwindow hmass
      (stage := 0) (nu := (0 : Fin 4)) (mu := mu) (hstage := by norm_num)
      holderU transportU
  have h1 :=
    integral_cmp89Eq249CompleteHolderMassUniformPartialProductIntegrand_stage_succ_draft
      (L := L) (j := j) (mass := mass) (a := a) (alpha := alpha)
      (rho := rho) ha hrho hamplitude hradius hwindow hmass
      (stage := 1) (nu := (1 : Fin 4)) (mu := mu) (hstage := by norm_num)
      holderU transportU
  have h2 :=
    integral_cmp89Eq249CompleteHolderMassUniformPartialProductIntegrand_stage_succ_draft
      (L := L) (j := j) (mass := mass) (a := a) (alpha := alpha)
      (rho := rho) ha hrho hamplitude hradius hwindow hmass
      (stage := 2) (nu := (2 : Fin 4)) (mu := mu) (hstage := by norm_num)
      holderU transportU
  have h3 :=
    integral_cmp89Eq249CompleteHolderMassUniformPartialProductIntegrand_stage_succ_draft
      (L := L) (j := j) (mass := mass) (a := a) (alpha := alpha)
      (rho := rho) ha hrho hamplitude hradius hwindow hmass
      (stage := 3) (nu := (3 : Fin 4)) (mu := mu) (hstage := by norm_num)
      holderU transportU
  exact h0.trans (h1.trans (h2.trans h3))

/-- The real complete Holder product integral equals its fully signed contour
integral at physical fine-lattice spacing, with no positive-mass premise. -/
theorem
    integral_cmp89Eq251ComplexStabilizedIntegrand_physicalFineHolder_eq_signed_massUniform_draft
    {L j : ℕ} [NeZero L] {mass a alpha rho : ℝ}
    (ha : 0 ≤ a) (hrho : 0 ≤ rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hwindow : CMP89Eq249CentralStabilizedComplexWindow a rho)
    (hmass : CMP89Eq251UniformMassWindow mass)
    (mu : Fin 4) (holderU transportU : Fin 4 → ℤ) :
    let xi := cmp89Eq249FineLatticeSpacing L j
    let holder := cmp89Eq249PhysicalFineLatticeDisplacement xi holderU
    let transport := cmp89Eq249PhysicalFineLatticeDisplacement xi transportU
    (∫ x, cmp89Eq251ComplexStabilizedIntegrand 4 L j mass a alpha
        (fun nu => (cmp89Eq251PhysicalBrillouinParameter x nu : ℂ))
        mu holder transport
      ∂(Measure.pi fun _ : Fin 4 =>
        volume.restrict (Set.uIoc 0 (2 * Real.pi)))) =
      ∫ x, cmp89Eq251ComplexStabilizedIntegrand 4 L j mass a alpha
        (cmp89Eq251SignedContourMomentum rho
          (cmp89Eq251PhysicalBrillouinParameter x) transport)
        mu holder transport
      ∂(Measure.pi fun _ : Fin 4 =>
        volume.restrict (Set.uIoc 0 (2 * Real.pi))) := by
  dsimp only
  have h :=
    integral_cmp89Eq249CompleteHolderMassUniformPartialProductIntegrand_zero_eq_four_draft
      (L := L) (j := j) (mass := mass) (a := a) (alpha := alpha)
      (rho := rho) ha hrho hamplitude hradius hwindow hmass
      mu holderU transportU
  simpa [cmp89Eq249CompleteHolderMassUniformPartialProductIntegrand_draft,
    cmp89Eq251EndpointPartialSignedContourMomentum_zero,
    cmp89Eq251EndpointPartialSignedContourMomentum_four] using h

end

end YangMills.RG
