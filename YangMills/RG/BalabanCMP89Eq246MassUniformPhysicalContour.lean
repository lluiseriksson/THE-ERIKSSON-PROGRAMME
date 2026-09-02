import YangMills.RG.BalabanCMP89Eq246DirectedPhysicalFineContourDictionary
import YangMills.RG.BalabanCMP89Eq246MassUniformAnalyticDomain

/-!
# PRE-VALIDATION: mass-uniform physical contour for the full CMP89 (2.46) kernel

Source is present, its promoted `.olean` has not yet been materialized, and
the result has not yet been compiler-verified.

This module telescopes the mass-uniform one-coordinate contour shift through
all four physical momentum coordinates and obtains the literal full-G decay
estimate at `mass = 0`.  It reuses the exact endpoint-selected contour and
the same source-built scalar windows; no abstract inverse, periodic Green,
generated operator, `B0`, or `delta0` is accepted from the caller.

It does not yet prove finite-grid periodization or identify the literal
Fourier kernel with the generated regional Green.  Consequently it does not
attain window 15, discharge a terminal row, or inhabit `TermSource`.

Source catalog key: `cmp89.local-green.fourier.2.34-2.51`.
-/

namespace YangMills.RG

open MeasureTheory

noncomputable section

/-- Every partial stage of the full-G contour is integrable uniformly on the
printed mass window. -/
theorem integrable_cmp89Eq246PhysicalFineToFineGreenPartialProductIntegrand_massUniform
    {L j : ℕ} [NeZero L] {mass a rho : ℝ}
    (ha : 0 ≤ a) (hrho : 0 ≤ rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hdenWindow : CMP89Eq249CentralStabilizedComplexWindow a rho)
    (hpairWindow : CMP89Eq249CentralAveragePairComplexWindow rho)
    (hmass : CMP89Eq251UniformMassWindow mass)
    (stage : ℕ) (target source : Fin 4 → ℤ) :
    Integrable
      (cmp89Eq246PhysicalFineToFineGreenPartialProductIntegrand
        L j mass a rho stage target source)
      (Measure.pi fun _ : Fin 4 =>
        volume.restrict (Set.uIoc 0 (2 * Real.pi))) := by
  have htwoPi : (0 : ℝ) ≤ 2 * Real.pi :=
    mul_nonneg (by norm_num) Real.pi_pos.le
  let displacement : Fin 4 → ℝ :=
    cmp89Eq249PhysicalFineLatticeDisplacement
      (cmp89Eq249FineLatticeSpacing L j) (fun mu => target mu - source mu)
  have hcont : ContinuousOn (fun x : Fin 4 → ℝ =>
      cmp89Eq246PhysicalFineToFineGreenIntegrand L j mass a
        (cmp89Eq251EndpointPartialSignedContourMomentum
          stage rho x displacement) target source)
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
    have houter : DifferentiableAt ℂ
        (fun w : Fin 4 → ℂ =>
          cmp89Eq246PhysicalFineToFineGreenIntegrand
            L j mass a w target source)
        (cmp89Eq251EndpointPartialSignedContourMomentum
          stage rho x displacement) := by
      simpa [cmp89Eq246PhysicalFineToFineGreenIntegrand] using
        (differentiableAt_cmp89Eq246StabilizedFineToFineGreenIntegrand_of_commonRadius_massUniform
          (L := L) (j := j) (mass := mass) (a := a) (rho := rho)
          ha hrho hamplitude hradius hdenWindow hpairWindow hmass
          (p := cmp89Eq251PhysicalBrillouinParameter x) hp
          (z := cmp89Eq251EndpointPartialSignedContourMomentum
            stage rho x displacement)
          (by
            intro nu
            exact cmp89Eq251EndpointPartialSignedContourMomentum_re
              stage rho x displacement nu)
          (abs_im_cmp89Eq251EndpointPartialSignedContourMomentum_le
            hrho stage x displacement)
          (targetEndpoint := cmp89Eq249PhysicalFineLatticeDisplacement
            (cmp89Eq249FineLatticeSpacing L j) target)
          (sourceEndpoint := cmp89Eq249PhysicalFineLatticeDisplacement
            (cmp89Eq249FineLatticeSpacing L j) source))
    have hinner : ContinuousAt (fun y : Fin 4 → ℝ =>
        cmp89Eq251EndpointPartialSignedContourMomentum
          stage rho y displacement) x :=
      (continuous_cmp89Eq251EndpointPartialSignedContourMomentum
        stage rho displacement).continuousAt
    have hcomp : ContinuousAt (fun y : Fin 4 → ℝ =>
        cmp89Eq246PhysicalFineToFineGreenIntegrand L j mass a
          (cmp89Eq251EndpointPartialSignedContourMomentum
            stage rho y displacement) target source) x := by
      exact ContinuousAt.comp
        (f := fun y : Fin 4 → ℝ =>
          cmp89Eq251EndpointPartialSignedContourMomentum
            stage rho y displacement)
        (g := fun w : Fin 4 → ℂ =>
          cmp89Eq246PhysicalFineToFineGreenIntegrand
            L j mass a w target source)
        houter.continuousAt hinner
    exact hcomp.continuousWithinAt
  have hIcc : IntegrableOn (fun x : Fin 4 → ℝ =>
      cmp89Eq246PhysicalFineToFineGreenIntegrand L j mass a
        (cmp89Eq251EndpointPartialSignedContourMomentum
          stage rho x displacement) target source)
      (Set.Icc (fun _ : Fin 4 => 0) (fun _ => 2 * Real.pi))
      (volume : Measure (Fin 4 → ℝ)) :=
    hcont.integrableOn_compact
      (isCompact_Icc : IsCompact
        (Set.Icc (fun _ : Fin 4 => 0) (fun _ => 2 * Real.pi)))
  have hIoc : IntegrableOn (fun x : Fin 4 → ℝ =>
      cmp89Eq246PhysicalFineToFineGreenIntegrand L j mass a
        (cmp89Eq251EndpointPartialSignedContourMomentum
          stage rho x displacement) target source)
      (Set.univ.pi fun _ : Fin 4 => Set.Ioc 0 (2 * Real.pi))
      (volume : Measure (Fin 4 → ℝ)) :=
    hIcc.congr_set_ae Measure.univ_pi_Ioc_ae_eq_Icc
  rw [IntegrableOn, volume_pi, Measure.restrict_pi_pi] at hIoc
  change Integrable (fun x : Fin 4 → ℝ =>
      cmp89Eq246PhysicalFineToFineGreenIntegrand L j mass a
        (cmp89Eq251EndpointPartialSignedContourMomentum
          stage rho x displacement) target source)
      (Measure.pi fun _ : Fin 4 =>
        volume.restrict (Set.uIoc 0 (2 * Real.pi)))
  simpa only [Set.uIoc_of_le htwoPi] using hIoc

/-- One coordinate transition in the mass-uniform full-G product telescope. -/
theorem integral_cmp89Eq246PhysicalFineToFineGreenPartialProductIntegrand_stage_succ_massUniform
    {L j : ℕ} [NeZero L] {mass a rho : ℝ}
    (ha : 0 ≤ a) (hrho : 0 ≤ rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hdenWindow : CMP89Eq249CentralStabilizedComplexWindow a rho)
    (hpairWindow : CMP89Eq249CentralAveragePairComplexWindow rho)
    (hmass : CMP89Eq251UniformMassWindow mass)
    (stage : ℕ) (nu : Fin 4) (hstage : stage = nu.val)
    (target source : Fin 4 → ℤ) :
    (∫ x, cmp89Eq246PhysicalFineToFineGreenPartialProductIntegrand
        L j mass a rho stage target source x
      ∂(Measure.pi fun _ : Fin 4 =>
        volume.restrict (Set.uIoc 0 (2 * Real.pi)))) =
      ∫ x, cmp89Eq246PhysicalFineToFineGreenPartialProductIntegrand
        L j mass a rho (stage + 1) target source x
      ∂(Measure.pi fun _ : Fin 4 =>
        volume.restrict (Set.uIoc 0 (2 * Real.pi))) := by
  let displacement : Fin 4 → ℝ :=
    cmp89Eq249PhysicalFineLatticeDisplacement
      (cmp89Eq249FineLatticeSpacing L j) (fun mu => target mu - source mu)
  have htwoPi : (0 : ℝ) ≤ 2 * Real.pi :=
    mul_nonneg (by norm_num) Real.pi_pos.le
  have hf :=
    integrable_cmp89Eq246PhysicalFineToFineGreenPartialProductIntegrand_massUniform
      (L := L) (j := j) (mass := mass) (a := a) (rho := rho)
      ha hrho hamplitude hradius hdenWindow hpairWindow hmass
      stage target source
  have hg :=
    integrable_cmp89Eq246PhysicalFineToFineGreenPartialProductIntegrand_massUniform
      (L := L) (j := j) (mass := mass) (a := a) (rho := rho)
      ha hrho hamplitude hradius hdenWindow hpairWindow hmass
      (stage + 1) target source
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
      (nu.insertNth 0 y) displacement
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
      stage rho (nu.insertNth 0 y) displacement k
  have himag : ∀ k, |(z k).im| ≤ rho := by
    intro k
    exact abs_im_cmp89Eq251EndpointPartialSignedContourMomentum_le
      hrho stage (nu.insertNth 0 y) displacement k
  have hnuImag : (z nu).im = 0 := by
    simp [z, cmp89Eq251EndpointPartialSignedContourMomentum_im, hstage]
  let eta : ℝ := rho * (SignType.sign (displacement nu) : ℝ)
  have heta : |eta| ≤ rho := by
    have h := abs_im_cmp89Eq251SignedContourMomentum_le hrho p displacement nu
    simpa [eta, cmp89Eq251SignedContourMomentum_im] using h
  have hshift :=
    intervalIntegral_cmp89Eq246PhysicalFineToFineGreenIntegrand_coordinateShift_massUniform
      (L := L) (j := j) (mass := mass) (a := a) (rho := rho)
      (eta := eta) ha hrho hamplitude hradius hdenWindow
      hpairWindow hmass heta nu hp hface hreal himag hnuImag target source
  simpa [cmp89Eq246PhysicalFineToFineGreenPartialProductIntegrand,
    displacement, z, eta,
    cmp89Eq251PhysicalCoordinateLine_partialSigned_eq stage rho nu hstage,
    cmp89Eq251PhysicalCoordinateLine_partialSigned_add_eta_eq
      stage rho nu hstage] using hshift

/-- The four literal coordinate transitions telescope uniformly on the mass
window. -/
theorem integral_cmp89Eq246PhysicalFineToFineGreenPartialProductIntegrand_zero_eq_four_massUniform
    {L j : ℕ} [NeZero L] {mass a rho : ℝ}
    (ha : 0 ≤ a) (hrho : 0 ≤ rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hdenWindow : CMP89Eq249CentralStabilizedComplexWindow a rho)
    (hpairWindow : CMP89Eq249CentralAveragePairComplexWindow rho)
    (hmass : CMP89Eq251UniformMassWindow mass)
    (target source : Fin 4 → ℤ) :
    (∫ x, cmp89Eq246PhysicalFineToFineGreenPartialProductIntegrand
        L j mass a rho 0 target source x
      ∂(Measure.pi fun _ : Fin 4 =>
        volume.restrict (Set.uIoc 0 (2 * Real.pi)))) =
      ∫ x, cmp89Eq246PhysicalFineToFineGreenPartialProductIntegrand
        L j mass a rho 4 target source x
      ∂(Measure.pi fun _ : Fin 4 =>
        volume.restrict (Set.uIoc 0 (2 * Real.pi))) := by
  have h0 :=
    integral_cmp89Eq246PhysicalFineToFineGreenPartialProductIntegrand_stage_succ_massUniform
      (L := L) (j := j) (mass := mass) (a := a) (rho := rho)
      ha hrho hamplitude hradius hdenWindow hpairWindow hmass
      (stage := 0) (nu := (0 : Fin 4)) (hstage := by norm_num) target source
  have h1 :=
    integral_cmp89Eq246PhysicalFineToFineGreenPartialProductIntegrand_stage_succ_massUniform
      (L := L) (j := j) (mass := mass) (a := a) (rho := rho)
      ha hrho hamplitude hradius hdenWindow hpairWindow hmass
      (stage := 1) (nu := (1 : Fin 4)) (hstage := by norm_num) target source
  have h2 :=
    integral_cmp89Eq246PhysicalFineToFineGreenPartialProductIntegrand_stage_succ_massUniform
      (L := L) (j := j) (mass := mass) (a := a) (rho := rho)
      ha hrho hamplitude hradius hdenWindow hpairWindow hmass
      (stage := 2) (nu := (2 : Fin 4)) (hstage := by norm_num) target source
  have h3 :=
    integral_cmp89Eq246PhysicalFineToFineGreenPartialProductIntegrand_stage_succ_massUniform
      (L := L) (j := j) (mass := mass) (a := a) (rho := rho)
      ha hrho hamplitude hradius hdenWindow hpairWindow hmass
      (stage := 3) (nu := (3 : Fin 4)) (hstage := by norm_num) target source
  exact h0.trans (h1.trans (h2.trans h3))

/-- The real full-G synthesis equals the fully signed contour uniformly on
the mass window. -/
theorem integral_cmp89Eq246PhysicalFineToFineGreenIntegrand_eq_signed_massUniform
    {L j : ℕ} [NeZero L] {mass a rho : ℝ}
    (ha : 0 ≤ a) (hrho : 0 ≤ rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hdenWindow : CMP89Eq249CentralStabilizedComplexWindow a rho)
    (hpairWindow : CMP89Eq249CentralAveragePairComplexWindow rho)
    (hmass : CMP89Eq251UniformMassWindow mass)
    (target source : Fin 4 → ℤ) :
    (∫ x, cmp89Eq246PhysicalFineToFineGreenIntegrand L j mass a
        (fun nu => (cmp89Eq251PhysicalBrillouinParameter x nu : ℂ))
        target source
      ∂(Measure.pi fun _ : Fin 4 =>
        volume.restrict (Set.uIoc 0 (2 * Real.pi)))) =
      ∫ x, cmp89Eq246PhysicalFineToFineGreenIntegrand L j mass a
        (cmp89Eq251SignedContourMomentum rho
          (cmp89Eq251PhysicalBrillouinParameter x)
          (cmp89Eq249PhysicalFineLatticeDisplacement
            (cmp89Eq249FineLatticeSpacing L j)
            (fun mu => target mu - source mu)))
        target source
      ∂(Measure.pi fun _ : Fin 4 =>
        volume.restrict (Set.uIoc 0 (2 * Real.pi))) := by
  have h :=
    integral_cmp89Eq246PhysicalFineToFineGreenPartialProductIntegrand_zero_eq_four_massUniform
      (L := L) (j := j) (mass := mass) (a := a) (rho := rho)
      ha hrho hamplitude hradius hdenWindow hpairWindow hmass
      target source
  simpa [cmp89Eq246PhysicalFineToFineGreenPartialProductIntegrand,
    cmp89Eq251EndpointPartialSignedContourMomentum_zero,
    cmp89Eq251EndpointPartialSignedContourMomentum_four] using h

/-- Literal fine endpoints identify the mass-uniform directed contour with
its real-slice value. -/
theorem cmp89Eq246DirectedNormalizedFullSolutionIntegral_physicalFine_eq_zero_massUniform
    {L j : ℕ} [NeZero L] {mass a rho : ℝ}
    (ha : 0 ≤ a) (hrho : 0 ≤ rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hdenWindow : CMP89Eq249CentralStabilizedComplexWindow a rho)
    (hpairWindow : CMP89Eq249CentralAveragePairComplexWindow rho)
    (hmass : CMP89Eq251UniformMassWindow mass)
    (target source : Fin 4 → ℤ) :
    cmp89Eq246DirectedNormalizedFullSolutionIntegral L j mass a rho
        (cmp89Eq249PhysicalFineLatticeDisplacement
          (cmp89Eq249FineLatticeSpacing L j) target)
        (cmp89Eq249PhysicalFineLatticeDisplacement
          (cmp89Eq249FineLatticeSpacing L j) source) =
      cmp89Eq246DirectedNormalizedFullSolutionIntegral L j mass a 0
        (cmp89Eq249PhysicalFineLatticeDisplacement
          (cmp89Eq249FineLatticeSpacing L j) target)
        (cmp89Eq249PhysicalFineLatticeDisplacement
          (cmp89Eq249FineLatticeSpacing L j) source) := by
  rw [cmp89Eq246DirectedNormalizedFullSolutionIntegral_eq_signedContour,
    cmp89Eq246DirectedNormalizedFullSolutionIntegral_zero_eq_realSlice]
  unfold cmp89Eq249NormalizedFourDimensionalBrillouinIntegral
  congr 1
  have hdisplacement :
      cmp89Eq249PhysicalFineLatticeDisplacement
          (cmp89Eq249FineLatticeSpacing L j)
          (fun mu => target mu - source mu) =
        fun mu =>
          cmp89Eq249PhysicalFineLatticeDisplacement
              (cmp89Eq249FineLatticeSpacing L j) target mu -
            cmp89Eq249PhysicalFineLatticeDisplacement
              (cmp89Eq249FineLatticeSpacing L j) source mu := by
    funext mu
    unfold cmp89Eq249PhysicalFineLatticeDisplacement
    push_cast
    ring
  unfold cmp89Eq249FourDimensionalBrillouinMeasure
  simpa [cmp89Eq246PhysicalFineToFineGreenIntegrand, hdisplacement] using
    (integral_cmp89Eq246PhysicalFineToFineGreenIntegrand_eq_signed_massUniform
      (L := L) (j := j) (mass := mass) (a := a) (rho := rho)
      ha hrho hamplitude hradius hdenWindow hpairWindow hmass
      target source).symm

/-- The physical directed full-G kernel is independent of the admissible
contour radius throughout the mass window. -/
theorem cmp89Eq246DirectedNormalizedPhysicalFineKernel_eq_zero_massUniform
    {L j : ℕ} [NeZero L] {mass a rho : ℝ}
    (ha : 0 ≤ a) (hrho : 0 ≤ rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hdenWindow : CMP89Eq249CentralStabilizedComplexWindow a rho)
    (hpairWindow : CMP89Eq249CentralAveragePairComplexWindow rho)
    (hmass : CMP89Eq251UniformMassWindow mass)
    (target source : Fin 4 → ℤ) :
    cmp89Eq246DirectedNormalizedPhysicalFineKernel
        L j mass a rho target source =
      cmp89Eq246DirectedNormalizedPhysicalFineKernel
        L j mass a 0 target source := by
  unfold cmp89Eq246DirectedNormalizedPhysicalFineKernel
  exact cmp89Eq246DirectedNormalizedFullSolutionIntegral_physicalFine_eq_zero_massUniform
    ha hrho hamplitude hradius hdenWindow hpairWindow hmass target source

/-- Exponential decay of the literal full-G Fourier synthesis, including the
physical mass-zero specialization. -/
theorem norm_cmp89Eq246NormalizedPhysicalFineToFineGreen_le_massUniform
    {L j : ℕ} [NeZero L] {mass a rho : ℝ}
    (ha : 0 ≤ a) (hrho : 0 ≤ rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hdenWindow : CMP89Eq249CentralStabilizedComplexWindow a rho)
    (hpairWindow : CMP89Eq249CentralAveragePairComplexWindow rho)
    (hmass : CMP89Eq251UniformMassWindow mass)
    (target source : Fin 4 → ℤ) :
    ‖cmp89Eq246NormalizedPhysicalFineToFineGreen
        L j mass a target source‖ ≤
      Real.exp (-((rho * cmp89Eq249FineLatticeSpacing L j) *
        cmp89Eq251LatticeL1Length (fun mu => target mu - source mu))) *
        cmp89Eq246DirectedFullSolutionSumBound L j a rho := by
  rw [← cmp89Eq246DirectedNormalizedPhysicalFineKernel_zero_eq_realGreenSynthesis]
  rw [← cmp89Eq246DirectedNormalizedPhysicalFineKernel_eq_zero_massUniform
    ha hrho hamplitude hradius hdenWindow hpairWindow hmass]
  exact norm_cmp89Eq246DirectedNormalizedPhysicalFineKernel_le
    ha hrho hradius hmass hdenWindow hpairWindow hamplitude target source

end

end YangMills.RG
