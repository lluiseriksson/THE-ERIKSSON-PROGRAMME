import YangMills.RG.BalabanCMP89Eq246DirectedFullSolutionSum
import YangMills.RG.BalabanCMP89Eq249NormalizedStabilizedEndpointIntegralBound

/-!
# Normalized directed Fourier synthesis below CMP89 (2.46)

This integrates the complete directed finite-alias solution with the literal
four-dimensional `(2*pi)^(-4)` normalization. The value bound deliberately
retains the `(L^j+1)^2` scale from the first component of CMP99 (3.42); only
its coefficient is meant to become uniform. Identification with the
generated periodic Green remains a separate inverse-uniqueness dictionary.

This module and its exact audit were cold-verified from source checkpoint
`887a726b4dc2d79925a67d16e9be4db935139e4d` in a fresh Colab Pro+ checkout.
-/

namespace YangMills.RG

open MeasureTheory

noncomputable section

/-- The normalized Brillouin integral of the complete target-phased alias
solution. -/
def cmp89Eq246DirectedNormalizedFullSolutionIntegral
    (L j : ℕ) [NeZero L] (mass a rho : ℝ)
    (targetEndpoint sourceEndpoint : Fin 4 → ℝ) : ℂ :=
  cmp89Eq249NormalizedFourDimensionalBrillouinIntegral fun x =>
    cmp89Eq246DirectedFullSolutionSum L j mass a rho
      (cmp89Eq251PhysicalBrillouinParameter x)
      targetEndpoint sourceEndpoint

/-- The normalized synthesis loses no further volume factor: the pointwise
common endpoint decay survives the literal `(2*pi)^(-4)` integration. -/
theorem norm_cmp89Eq246DirectedNormalizedFullSolutionIntegral_le
    {L j : ℕ} [NeZero L] {mass a rho : ℝ}
    (ha : 0 ≤ a) (hrho : 0 ≤ rho)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hmass : CMP89Eq251UniformMassWindow mass)
    (hstabilized : CMP89Eq249CentralStabilizedComplexWindow a rho)
    (hpair : CMP89Eq249CentralAveragePairComplexWindow rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    (targetEndpoint sourceEndpoint : Fin 4 → ℝ) :
    let displacement := fun mu => targetEndpoint mu - sourceEndpoint mu
    ‖cmp89Eq246DirectedNormalizedFullSolutionIntegral
        L j mass a rho targetEndpoint sourceEndpoint‖ ≤
      Real.exp (-(rho * cmp89Eq251DisplacementL1 displacement)) *
        cmp89Eq246DirectedFullSolutionSumBound L j a rho := by
  dsimp only
  let displacement := fun mu => targetEndpoint mu - sourceEndpoint mu
  let C := Real.exp (-(rho * cmp89Eq251DisplacementL1 displacement)) *
    cmp89Eq246DirectedFullSolutionSumBound L j a rho
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
  have hmem : ∀ᵐ x ∂cmp89Eq249FourDimensionalBrillouinMeasure, x ∈ cube := by
    rw [hmeasure]
    exact ae_restrict_mem hcube
  have hf : ∀ᵐ x ∂cmp89Eq249FourDimensionalBrillouinMeasure,
      ‖cmp89Eq246DirectedFullSolutionSum L j mass a rho
        (cmp89Eq251PhysicalBrillouinParameter x)
        targetEndpoint sourceEndpoint‖ ≤ C := by
    filter_upwards [hmem] with x hx
    have hp : ∀ nu, |cmp89Eq251PhysicalBrillouinParameter x nu| ≤
        Real.pi := by
      intro nu
      have hxnu : x nu ∈ Set.Ioc 0 (2 * Real.pi) := hx nu (by simp)
      have hxLower := hxnu.1
      have hxUpper := hxnu.2
      rw [abs_le]
      simp only [cmp89Eq251PhysicalBrillouinParameter]
      constructor <;> linarith [Real.pi_pos]
    simpa [C, displacement] using
      (norm_cmp89Eq246DirectedFullSolutionSum_signedContour_le
        (L := L) (j := j) (mass := mass) (a := a) (rho := rho)
        ha hrho hradius hmass hstabilized hpair hamplitude hp
        targetEndpoint sourceEndpoint)
  simpa [cmp89Eq246DirectedNormalizedFullSolutionIntegral, C] using
    (norm_cmp89Eq249NormalizedFourDimensionalBrillouinIntegral_le hf)

end

end YangMills.RG
