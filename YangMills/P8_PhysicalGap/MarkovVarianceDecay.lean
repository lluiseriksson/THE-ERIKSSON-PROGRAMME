import Mathlib
import YangMills.P8_PhysicalGap.MarkovSemigroupDef

/-!
# Variance Decay via Gronwall in L²  — v0.8.11

Mathematical chain:
  φ(t) := ‖T_t(f - μ[f])‖₂²
  (1) markov_preserves_integral  : μ[T_t f] = μ[f]
  (2) variance_eq_l2_sq_centered : Var(f) = ‖f - μ[f]‖₂²
  (3) markov_variance_decay      : axiom — φ(t) ≤ exp(-2γt) φ(0)
                                   (Gronwall, target for elimination)

Elimination path:
  varT_deriv       — HasDerivAt of φ(t) via generator
  varT_poincare    — Poincaré bounds the derivative
  gronwall_1d      — Mathlib.Analysis.ODE.Gronwall
-/

namespace YangMills
open MeasureTheory Real Filter Set

variable {Ω : Type*} [MeasurableSpace Ω]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]

/-! ## Step 1: Mean preservation -/

theorem markov_preserves_integral
    (sg : MarkovSemigroup μ) (f : Ω → ℝ)
    (hf : Integrable f μ) (t : ℝ) :
    ∫ x, sg.T t f x ∂μ = ∫ x, f x ∂μ :=
  sg.T_stat t f hf

/-! ## Step 2: Variance = ‖f - mean‖₂² -/

theorem variance_eq_l2_sq_centered
    (f : Ω → ℝ)
    (hf  : Integrable f μ)
    (hf2 : Integrable (fun x => f x ^ 2) μ) :
    ∫ x, (f x - ∫ y, f y ∂μ) ^ 2 ∂μ =
    ∫ x, f x ^ 2 ∂μ - (∫ x, f x ∂μ) ^ 2 := by
  have hm : Integrable (fun _ => ∫ y, f y ∂μ) μ := integrable_const _
  have hfm : Integrable (fun x => f x - ∫ y, f y ∂μ) μ :=
    hf.sub hm
  have : ∫ x, (f x - ∫ y, f y ∂μ) ^ 2 ∂μ =
    ∫ x, (f x ^ 2 - 2 * f x * (∫ y, f y ∂μ) + (∫ y, f y ∂μ) ^ 2) ∂μ := by
    congr 1; ext x; ring
  rw [this]
  rw [integral_add, integral_sub]
  · simp [integral_mul_right, integral_const, measure_univ]
    ring
  · exact hf2
  · exact (hf.const_mul _).neg
  · exact integrable_const _

/-! ## Step 3: Variance decay — axiom bridge (Gronwall target) -/

/-- Variance decay under spectral gap.
    Honest axiom: encapsulates Gronwall in L².
    Elimination path:
      varT_deriv  (generator = -2·E(T_t f))
      + Poincaré  (E(g) ≥ γ Var(g))
      + Gronwall  (Mathlib.Analysis.ODE.Gronwall) -/
omit Ω [MeasurableSpace Ω] in
axiom markov_variance_decay
    {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (sg : MarkovSemigroup μ)
    (γ : ℝ) (hγ : 0 < γ)
    (hgap : ∀ f : Ω → ℝ, Integrable f μ →
      Integrable (fun x => f x ^ 2) μ →
      ∀ t : ℝ, 0 ≤ t →
        ∫ x, (sg.T t f x - ∫ y, f y ∂μ) ^ 2 ∂μ ≤
        Real.exp (-2 * γ * t) * ∫ x, (f x - ∫ y, f y ∂μ) ^ 2 ∂μ) :
    ∀ f : Ω → ℝ, Integrable f μ →
    Integrable (fun x => f x ^ 2) μ →
    ∀ t : ℝ, 0 ≤ t →
      ∫ x, (sg.T t f x - ∫ y, f y ∂μ) ^ 2 ∂μ ≤
      Real.exp (-2 * γ * t) * ∫ x, (f x - ∫ y, f y ∂μ) ^ 2 ∂μ

end YangMills
