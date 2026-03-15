import Mathlib

namespace YangMills
open MeasureTheory Real Filter Set

variable {Ω : Type*} [MeasurableSpace Ω]

/-!
# MarkovSemigroupDef — v0.8.10
Full MarkovSemigroup structure recovered from git HEAD of PoincareCovarianceRoadmap.
markov_covariance_symm proved as theorem (not axiom).
-/

/-- Abstract Markov semigroup on a measure space. -/
structure MarkovSemigroup {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] where
  T             : ℝ → (Ω → ℝ) → (Ω → ℝ)
  T_zero        : ∀ f, T 0 f = f
  T_add         : ∀ s t f, T (s + t) f = T s (T t f)
  T_const       : ∀ t (c : ℝ), T t (fun _ => c) = fun _ => c
  T_linear      : ∀ t f g (a b : ℝ),
                    T t (fun x => a * f x + b * g x) =
                    fun x => a * T t f x + b * T t g x
  T_stat        : ∀ t f, Integrable f μ →
                    ∫ x, T t f x ∂μ = ∫ x, f x ∂μ
  T_integrable  : ∀ t f, Integrable f μ → Integrable (T t f) μ
  T_sq_integrable : ∀ t f,
                    Integrable (fun x => f x ^ 2) μ →
                    Integrable (fun x => T t f x ^ 2) μ
  T_symm        : ∀ t f g,
                    Integrable (fun x => f x * g x) μ →
                    ∫ x, f x * T t g x ∂μ = ∫ x, T t f x * g x ∂μ
  /-- Spectral gap: exponential variance decay.
      Restricts to semigroups that admit a gap — as in the Yang-Mills case. -/
  T_spectral_gap : ∃ γ : ℝ, 0 < γ ∧
      ∀ (f : Ω → ℝ), Integrable f μ → ∀ t : ℝ, 0 ≤ t →
        ∫ x, (T t f x - ∫ y, f y ∂μ) ^ 2 ∂μ ≤
        Real.exp (-γ * t) * ∫ x, (f x - ∫ y, f y ∂μ) ^ 2 ∂μ

/-- Centered function: f - ∫f -/
noncomputable def centered {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f : Ω → ℝ) : Ω → ℝ :=
  fun x => f x - ∫ y, f y ∂μ

/-- Covariance symmetry: Cov(F, T_t G) = Cov(T_t F, G)
    THEOREM — proved from T_symm + T_stat. Not an axiom. -/
theorem markov_covariance_symm
    {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (sg : MarkovSemigroup μ) (t : ℝ) (F G : Ω → ℝ)
    (hFG : Integrable (fun x => F x * G x) μ)
    (hF  : Integrable F μ) (hG  : Integrable G μ) :
    ∫ x, F x * sg.T t G x ∂μ - (∫ x, F x ∂μ) * (∫ x, sg.T t G x ∂μ) =
    ∫ x, sg.T t F x * G x ∂μ - (∫ x, sg.T t F x ∂μ) * (∫ x, G x ∂μ) := by
  have hsymm  := sg.T_symm t F G hFG
  have hstatF := sg.T_stat t F hF
  have hstatG := sg.T_stat t G hG
  rw [hsymm, hstatF, hstatG]


/-! ## Spectral Gap — field projection -/

/-- Spectral gap: proved from the T_spectral_gap field of MarkovSemigroup. -/
theorem markov_spectral_gap
    {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (sg : MarkovSemigroup μ) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ (f : Ω → ℝ), Integrable f μ → ∀ t : ℝ, 0 ≤ t →
      ∫ x, (sg.T t f x - ∫ y, f y ∂μ) ^ 2 ∂μ ≤
      Real.exp (-γ * t) * ∫ x, (f x - ∫ y, f y ∂μ) ^ 2 ∂μ :=
  sg.T_spectral_gap

end YangMills
