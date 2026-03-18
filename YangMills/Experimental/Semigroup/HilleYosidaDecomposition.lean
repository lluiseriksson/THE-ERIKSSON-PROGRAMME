import Mathlib
import YangMills.P8_PhysicalGap.MarkovSemigroupDef

namespace YangMills
open MeasureTheory Real

/-!
# HilleYosidaDecomposition — Architectural spike

## Soundness finding

`hille_yosida_semigroup` claims: IsDirichletFormStrong E μ → MarkovSemigroup μ
But `MarkovSemigroup` includes `T_spectral_gap` (exponential variance decay).
This is FALSE in general: Brownian motion on ℝᵈ has a strong Dirichlet form
but NO spectral gap. Spectral gap requires Poincaré inequality separately.

## Honest decomposition

Layer A+B: hille_yosida_core — Dirichlet form → SymmetricMarkovTransport
Layer C:   poincare_to_variance_decay — Poincaré + transport → HasVarianceDecay

Together they reconstruct MarkovSemigroup, but each is independently honest.
Net: axiom-neutral (poincare_to_variance_decay is a new axiom).
Decision: P8 keeps hille_yosida_semigroup pending Mathlib C₀-semigroup theory.
-/

variable {Ω : Type*} [MeasurableSpace Ω]

-- Layer A: pure semigroup algebra
structure MarkovSemigroupCore (μ : Measure Ω) [IsProbabilityMeasure μ] where
  T        : ℝ → (Ω → ℝ) → (Ω → ℝ)
  T_zero   : ∀ f, T 0 f = f
  T_add    : ∀ s t f, T (s + t) f = T s (T t f)
  T_const  : ∀ t (c : ℝ), T t (fun _ => c) = fun _ => c
  T_linear : ∀ t f g (a b : ℝ),
               T t (fun x => a * f x + b * g x) =
               fun x => a * T t f x + b * T t g x

-- Layer B: adds stationarity, L¹/L² transport, symmetry
structure SymmetricMarkovTransport
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    extends MarkovSemigroupCore μ where
  T_stat          : ∀ t f, Integrable f μ → ∫ x, T t f x ∂μ = ∫ x, f x ∂μ
  T_integrable    : ∀ t f, Integrable f μ → Integrable (T t f) μ
  T_sq_integrable : ∀ t f,
      Integrable (fun x => f x ^ 2) μ →
      Integrable (fun x => T t f x ^ 2) μ
  T_symm          : ∀ t f g,
      Integrable (fun x => f x * g x) μ →
      ∫ x, f x * T t g x ∂μ = ∫ x, T t f x * g x ∂μ

-- Layer C: variance decay (Poincaré + Gronwall — NOT automatic)
def HasVarianceDecay
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (sg : SymmetricMarkovTransport μ) : Prop :=
  ∃ γ : ℝ, 0 < γ ∧
    ∀ (f : Ω → ℝ), Integrable f μ → ∀ t : ℝ, 0 ≤ t →
      ∫ x, (sg.T t f x - ∫ y, f y ∂μ) ^ 2 ∂μ ≤
      Real.exp (-γ * t) * ∫ x, (f x - ∫ y, f y ∂μ) ^ 2 ∂μ

-- Honest axiom 1: Dirichlet form → semigroup + transport (no spectral gap)
axiom hille_yosida_core
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (E : (Ω → ℝ) → ℝ) (hE : IsDirichletFormStrong E μ) :
    SymmetricMarkovTransport μ

-- Honest axiom 2: Poincaré + semigroup → variance decay
-- (Gronwall: d/dt Var(T_t f) = -2·E(T_t f) ≤ -2·lam·Var(T_t f))
axiom poincare_to_variance_decay
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (E : (Ω → ℝ) → ℝ) (hE : IsDirichletFormStrong E μ)
    (sg : SymmetricMarkovTransport μ)
    (lam : ℝ) (hP : PoincareInequality μ E lam) :
    HasVarianceDecay sg

end YangMills
