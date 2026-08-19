/-
STATIC DRAFT ONLY -- NOT COMPILER-VERIFIED.

Mass-uniform source-normalized bound for the literal stabilized Fourier
Green.  The contour equality is constructed by the Green-specific four-stage
telescope, and the pointwise majorant is the literal Green amplitude bound.
The source normalization cancels the physical cube volume exactly.

No operator dictionary, regional `B0`, window-15 attainment or terminal
field is asserted here.
-/

import YangMills.RG.BalabanCMP89Eq248GreenProductContourTelescope
import YangMills.RG.BalabanCMP89Eq248MassUniformGreenBound

namespace YangMills.RG

open MeasureTheory

noncomputable section

/-- The literal normalized real Green integral equals its own fully signed
mass-uniform contour integral. -/
theorem cmp89Eq248NormalizedFineLatticeStabilizedFourierGreen_eq_signed_massUniform_draft
    {L j : ℕ} [NeZero L] {mass a rho : ℝ}
    (ha : 0 ≤ a) (hrho : 0 ≤ rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hwindow : CMP89Eq249CentralStabilizedComplexWindow a rho)
    (hmass : CMP89Eq251UniformMassWindow mass)
    (endpointU : Fin 4 → ℤ) :
    cmp89Eq248NormalizedFineLatticeStabilizedFourierGreen
        L j mass a endpointU =
      cmp89Eq249NormalizedFourDimensionalBrillouinIntegral
        (fun x => cmp89Eq248ComplexStabilizedGreenEndpointIntegrand
          4 L j mass a
          (cmp89Eq251SignedContourMomentum rho
            (cmp89Eq251PhysicalBrillouinParameter x)
            (cmp89Eq249PhysicalFineLatticeDisplacement
              (((L ^ j : ℕ) : ℝ)⁻¹) endpointU))
          (cmp89Eq249PhysicalFineLatticeDisplacement
            (((L ^ j : ℕ) : ℝ)⁻¹) endpointU)) := by
  have h :=
    integral_cmp89Eq248ComplexStabilizedGreenEndpointIntegrand_physicalFine_eq_signed_massUniform_draft
      (L := L) (j := j) (mass := mass) (a := a) (rho := rho)
      ha hrho hamplitude hradius hwindow hmass endpointU
  unfold cmp89Eq248NormalizedFineLatticeStabilizedFourierGreen
    cmp89Eq249NormalizedFourDimensionalBrillouinIntegral
    cmp89Eq249FourDimensionalBrillouinMeasure cmp89Eq249FineLatticeSpacing
  rw [h]

/-- Exact physical Green coefficient bound with mass-uniform amplitude and
fine-lattice exponential decay. -/
theorem norm_cmp89Eq248NormalizedFineLatticeStabilizedFourierGreen_le_massUniform_draft
    {L j : ℕ} [NeZero L] {mass a rho : ℝ}
    (ha : 0 ≤ a) (hrho : 0 ≤ rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hwindow : CMP89Eq249CentralStabilizedComplexWindow a rho)
    (hmass : CMP89Eq251UniformMassWindow mass)
    (endpointU : Fin 4 → ℤ) :
    ‖cmp89Eq248NormalizedFineLatticeStabilizedFourierGreen
        L j mass a endpointU‖ ≤
      Real.exp (-(rho * cmp89Eq251DisplacementL1
        (cmp89Eq249PhysicalFineLatticeDisplacement
          (((L ^ j : ℕ) : ℝ)⁻¹) endpointU))) *
        cmp89Eq248ComplexStabilizedGreenAmplitudeBound_draft a rho := by
  rw [cmp89Eq248NormalizedFineLatticeStabilizedFourierGreen_eq_signed_massUniform_draft
    (L := L) (j := j) (mass := mass) (a := a) (rho := rho)
    ha hrho hamplitude hradius hwindow hmass]
  apply norm_cmp89Eq249NormalizedFourDimensionalBrillouinIntegral_le
  have htwoPi : (0 : ℝ) ≤ 2 * Real.pi :=
    mul_nonneg (by norm_num) Real.pi_pos.le
  let cube : Set (Fin 4 → ℝ) :=
    Set.univ.pi fun _ : Fin 4 => Set.Ioc 0 (2 * Real.pi)
  have hmeasure :
      cmp89Eq249FourDimensionalBrillouinMeasure =
        (volume : Measure (Fin 4 → ℝ)).restrict cube := by
    dsimp [cmp89Eq249FourDimensionalBrillouinMeasure, cube]
    rw [volume_pi, Measure.restrict_pi_pi]
    simp [Set.uIoc_of_le htwoPi]
  have hcube : MeasurableSet cube := by
    exact MeasurableSet.pi (Set.to_countable Set.univ) fun _ _ =>
      measurableSet_Ioc
  have hmem : ∀ᵐ x ∂cmp89Eq249FourDimensionalBrillouinMeasure,
      x ∈ cube := by
    rw [hmeasure]
    exact ae_restrict_mem hcube
  filter_upwards [hmem] with x hx
  have hp : ∀ nu, |cmp89Eq251PhysicalBrillouinParameter x nu| ≤
      Real.pi := by
    intro nu
    have hxnu : x nu ∈ Set.Ioc 0 (2 * Real.pi) := hx nu (by simp)
    rw [abs_le]
    simp only [cmp89Eq251PhysicalBrillouinParameter]
    constructor <;> linarith [hxnu.1, hxnu.2, Real.pi_pos]
  exact
    norm_cmp89Eq248ComplexStabilizedGreenEndpointIntegrand_signedContour_le_massUniform_draft
      (L := L) (j := j) (mass := mass) (a := a) (rho := rho)
      ha hmass hrho hradius hwindow hamplitude hp
      (cmp89Eq249PhysicalFineLatticeDisplacement
        (((L ^ j : ℕ) : ℝ)⁻¹) endpointU)

end

end YangMills.RG
