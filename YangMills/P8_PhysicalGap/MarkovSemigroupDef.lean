import Mathlib
import YangMills.P8_PhysicalGap.LSIDefinitions

namespace YangMills
open MeasureTheory Real Filter Set

variable {Ω : Type*} [MeasurableSpace Ω]

/-!
# MarkovSemigroupDef — v0.8.10
Full MarkovSemigroup structure recovered from git HEAD of PoincareCovarianceRoadmap.
markov_covariance_symm proved as theorem (not axiom).
-/

/-- Symmetric Markov transport: Layer A+B only.
    Semigroup algebra + measure-theoretic transport.
    Does NOT include spectral gap (which requires Poincaré separately). -/
structure SymmetricMarkovTransport {Ω : Type*} [MeasurableSpace Ω]
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

/-- Variance decay: Layer C — spectral gap property.
    Shape matches markov_variance_decay exactly (hf2 + exp(-2γt)).
    Requires Poincaré inequality. NOT automatic from Dirichlet form.
    (Brownian motion on ℝᵈ: strong Dirichlet form but no spectral gap.) -/
def HasVarianceDecay {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (sg : SymmetricMarkovTransport μ) : Prop :=
  ∃ γ : ℝ, 0 < γ ∧
    ∀ (f : Ω → ℝ), Integrable f μ →
    Integrable (fun x => f x ^ 2) μ →
    ∀ t : ℝ, 0 ≤ t →
      ∫ x, (sg.T t f x - ∫ y, f y ∂μ) ^ 2 ∂μ ≤
      Real.exp (-2 * γ * t) * ∫ x, (f x - ∫ y, f y ∂μ) ^ 2 ∂μ

/-- Full Markov semigroup: Layer A+B+C (transport + spectral gap).
    Spectral gap is the Yang-Mills-specific addition. -/
structure MarkovSemigroup {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    extends SymmetricMarkovTransport μ where
  /-- Spectral gap: exponential variance decay.
      NOT automatic from Dirichlet form — requires Poincaré inequality.
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
    (sg : SymmetricMarkovTransport μ) (t : ℝ) (F G : Ω → ℝ)
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


/-! ## Hille-Yosida: Dirichlet form → Markov semigroup -/

/-- **MATHLIB GAP — Beurling-Deny / Hille-Yosida correspondence.**

Every symmetric closed strong Dirichlet form `(E, μ)` on a probability space
generates a unique strongly continuous self-adjoint Markov semigroup on L²(μ).
    Returns SymmetricMarkovTransport (Layer A+B): transport without spectral gap.
    Spectral gap requires Poincaré separately (Layer C).

Mathematical status: Two classical theorems composed:
1. Beurling-Deny (1958) / Fukushima (1971): Symmetric closed Dirichlet form →
   unique strongly continuous symmetric Markov semigroup.
   Ref: Fukushima-Oshima-Takeda, Dirichlet Forms and Symmetric Markov Processes,
   Theorem 1.3.1.
2. Spectral gap from Poincaré: d/dt Var(Tₜf) = -2·E(Tₜf) + Gronwall.
   Ref: Bakry-Gentil-Ledoux, Analysis and Geometry of Markov Diffusion
   Operators, Proposition 4.2.5.

Why NOT a Clay gap: Standard mathematics known for 70+ years. Will become a
theorem when Mathlib gains C₀-semigroup theory (Hille-Yosida for unbounded
operators on Banach spaces).

Formalization gap: Mathlib 4.29 has `Mathlib.Analysis.ODE.Gronwall` (scalar)
but lacks the full operator semigroup theory: C₀-semigroups, resolvent
estimates, generator domains, and the Dirichlet form ↔ semigroup correspondence.

Used exactly once: in `sz_lsi_to_clustering` (LSItoSpectralGap.lean) to
construct the Markov semigroup needed by the Stroock-Zegarlinski bridge. -/
axiom hille_yosida_semigroup
    {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (E : (Ω → ℝ) → ℝ) (hE : IsDirichletFormStrong E μ) :
    SymmetricMarkovTransport μ

end YangMills
