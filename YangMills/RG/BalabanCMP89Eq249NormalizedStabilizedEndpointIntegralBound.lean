/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP89Eq251ComplexStabilizedEndpointBound

/-!
# PRE-VALIDATION: source-normalized endpoint integral below CMP89 (2.49)

Source is present, but this module's `.olean` has not yet been materialized
and its declarations have not yet been verified by the compiler.

CMP89 (2.49), visually checked on printed page 585, places `(2*pi)^(-d)`
outside the integral on `[-pi,pi]^d`. In four dimensions the translated
parameter cube `[0,2*pi]^4` has volume `(2*pi)^4`; this module keeps both
factors literal and cancels them exactly.

The specialized theorem integrates one stabilized endpoint on its own signed
contour. It does not recombine the two endpoints, absorb the separate
`exp rho` one-link cost, transport to localization owners, construct the
complete physical `B0`, attain window 15, discharge rows 23--24 or inhabit a
`TermSource`.
-/

namespace YangMills.RG

open MeasureTheory

noncomputable section

/-- Product Lebesgue measure on the translated four-dimensional Brillouin
cube. -/
def cmp89Eq249FourDimensionalBrillouinMeasure : Measure (Fin 4 → ℝ) :=
  Measure.pi fun _ : Fin 4 =>
    volume.restrict (Set.uIoc 0 (2 * Real.pi))

instance cmp89Eq249FourDimensionalBrillouinMeasure_isFinite :
    IsFiniteMeasure cmp89Eq249FourDimensionalBrillouinMeasure := by
  refine ⟨?_⟩
  simp [cmp89Eq249FourDimensionalBrillouinMeasure, Measure.pi_univ]
  exact ENNReal.mul_lt_top (by norm_num) ENNReal.ofReal_lt_top

/-- The source normalization `(2*pi)^(-4)` applied to an integral over the
translated Brillouin cube. -/
def cmp89Eq249NormalizedFourDimensionalBrillouinIntegral
    (f : (Fin 4 → ℝ) → ℂ) : ℂ :=
  ((((2 * Real.pi) ^ 4)⁻¹ : ℝ) : ℂ) *
    ∫ x, f x ∂cmp89Eq249FourDimensionalBrillouinMeasure

/-- The translated four-dimensional Brillouin cube has exactly the volume
that cancels the source normalization in (2.49). -/
theorem cmp89Eq249FourDimensionalBrillouinMeasure_real_univ :
    cmp89Eq249FourDimensionalBrillouinMeasure.real Set.univ =
      (2 * Real.pi) ^ 4 := by
  have htwoPi : (0 : ℝ) ≤ 2 * Real.pi :=
    mul_nonneg (by norm_num) Real.pi_pos.le
  simp [cmp89Eq249FourDimensionalBrillouinMeasure, Measure.pi_univ,
    measureReal_def, ENNReal.toReal_ofReal', Set.uIoc_of_le htwoPi,
    max_eq_left Real.pi_pos.le]

/-- A constant pointwise bound on the translated Brillouin cube loses no
factor after the literal source normalization is applied. -/
theorem norm_cmp89Eq249NormalizedFourDimensionalBrillouinIntegral_le
    {f : (Fin 4 → ℝ) → ℂ} {C : ℝ}
    (hf : ∀ᵐ x ∂cmp89Eq249FourDimensionalBrillouinMeasure, ‖f x‖ ≤ C) :
    ‖cmp89Eq249NormalizedFourDimensionalBrillouinIntegral f‖ ≤ C := by
  have hint := MeasureTheory.norm_integral_le_of_norm_le_const
    (μ := cmp89Eq249FourDimensionalBrillouinMeasure) hf
  rw [cmp89Eq249FourDimensionalBrillouinMeasure_real_univ] at hint
  rw [cmp89Eq249NormalizedFourDimensionalBrillouinIntegral, norm_mul,
    Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_pow,
    abs_of_pos (mul_pos (by norm_num) Real.pi_pos)]
  have hscale : 0 ≤ ((2 * Real.pi) ^ 4)⁻¹ := by positivity
  calc
    ((2 * Real.pi) ^ 4)⁻¹ * ‖∫ x, f x
        ∂cmp89Eq249FourDimensionalBrillouinMeasure‖ ≤
        ((2 * Real.pi) ^ 4)⁻¹ * (C * (2 * Real.pi) ^ 4) :=
      mul_le_mul_of_nonneg_left hint hscale
    _ = C := by field_simp

/-- One complete stabilized endpoint, integrated with the literal source
normalization, is bounded by its exact signed lattice decay times the explicit
phase-free-amplitude and reciprocal majorant. -/
theorem norm_cmp89Eq249NormalizedStabilizedEndpointIntegral_le
    {L j : ℕ} [NeZero L] {mass a alpha rho : ℝ}
    (ha : 0 ≤ a) (hmassPos : 0 < mass) (hrho : 0 ≤ rho)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hmass : CMP89Eq251UniformMassWindow mass)
    (hwindow : CMP89Eq249CentralStabilizedComplexWindow a rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    (mu : Fin 4) {holderU endpointU : Fin 4 → ℤ}
    (hholder : CMP89Eq251UnitLatticeBondDisplacement holderU) :
    ‖cmp89Eq249NormalizedFourDimensionalBrillouinIntegral
        (fun x => cmp89Eq251ComplexStabilizedEndpointIntegrand
          4 L j mass a alpha
          (cmp89Eq251SignedContourMomentum rho
            (cmp89Eq251PhysicalBrillouinParameter x)
            (cmp89Eq251LatticeDisplacement endpointU)) mu
          (cmp89Eq251LatticeDisplacement holderU)
          (cmp89Eq251LatticeDisplacement endpointU))‖ ≤
      cmp89SignedLatticeL1ExponentialWeight rho endpointU *
        cmp89Eq251ComplexStabilizedEndpointAmplitudeBound a rho := by
  let C : ℝ :=
    cmp89SignedLatticeL1ExponentialWeight rho endpointU *
      cmp89Eq251ComplexStabilizedEndpointAmplitudeBound a rho
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
      ‖cmp89Eq251ComplexStabilizedEndpointIntegrand
        4 L j mass a alpha
        (cmp89Eq251SignedContourMomentum rho
          (cmp89Eq251PhysicalBrillouinParameter x)
          (cmp89Eq251LatticeDisplacement endpointU)) mu
        (cmp89Eq251LatticeDisplacement holderU)
        (cmp89Eq251LatticeDisplacement endpointU)‖ ≤ C := by
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
    simpa [C] using
      (norm_cmp89Eq251ComplexStabilizedEndpointIntegrand_signedContour_le
        (L := L) (j := j) (mass := mass) (a := a) (alpha := alpha)
        (rho := rho) ha hmassPos hrho hradius hmass hwindow hamplitude hp mu
        hholder)
  exact norm_cmp89Eq249NormalizedFourDimensionalBrillouinIntegral_le hf

end

end YangMills.RG
