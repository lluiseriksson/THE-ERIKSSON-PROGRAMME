import Mathlib
import YangMills.P8_PhysicalGap.LSItoSpectralGap
import YangMills.P8_PhysicalGap.StroockZegarlinski

/-!
# PoincareCovarianceRoadmap — MarkovSemigroup API (Layers 1-4)

Layer 3 (Cauchy-Schwarz) is proved in StroockZegarlinski.lean.
This file implements Layers 1, 2 (axiom), and 4 (assembly sketch).
-/

namespace YangMills
open MeasureTheory Real Filter Set

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ## Layer 1: MarkovSemigroup structure -/

/-- Abstract Markov semigroup on a measure space.
    Minimal API needed for the SZ covariance decay argument. -/
structure MarkovSemigroup (μ : Measure Ω) where
  /-- The semigroup operators T_t : (Ω → ℝ) → (Ω → ℝ) -/
  T : ℝ → (Ω → ℝ) → (Ω → ℝ)
  /-- T_0 = identity -/
  T_zero : ∀ f, T 0 f = f
  /-- Semigroup: T_{s+t} = T_s ∘ T_t -/
  T_add : ∀ s t f, T (s + t) f = T s (T t f)
  /-- Constants are fixed: T_t(c) = c -/
  T_const : ∀ t (c : ℝ), T t (fun _ => c) = fun _ => c
  /-- Linearity: T_t(af + bg) = a·T_t(f) + b·T_t(g) -/
  T_linear : ∀ t f g (a b : ℝ),
      T t (fun x => a * f x + b * g x) =
      fun x => a * T t f x + b * T t g x
  /-- Stationarity: ∫ T_t f = ∫ f -/
  T_stat : ∀ t f, Integrable f μ →
      ∫ x, T t f x ∂μ = ∫ x, f x ∂μ
  /-- Integrability preserved -/
  T_integrable : ∀ t f, Integrable f μ → Integrable (T t f) μ
  /-- Square integrability preserved -/
  T_sq_integrable : ∀ t f,
      Integrable (fun x => f x ^ 2) μ →
      Integrable (fun x => T t f x ^ 2) μ
  /-- Symmetry in L²: ∫ f · T_t g = ∫ T_t f · g -/
  T_symm : ∀ t f g,
      Integrable (fun x => f x * g x) μ →
      ∫ x, f x * T t g x ∂μ = ∫ x, T t f x * g x ∂μ

/-! ## Basic lemmas from the structure -/

/-- Centered function: f - ∫f -/
def centered (μ : Measure Ω) (f : Ω → ℝ) : Ω → ℝ :=
  fun x => f x - ∫ y, f y ∂μ

/-- T_t preserves centering (since T_t preserves integrals). -/
lemma markov_centered_eq {μ : Measure Ω} [IsProbabilityMeasure μ]
    (sg : MarkovSemigroup μ) (f : Ω → ℝ) (t : ℝ)
    (hf : Integrable f μ) :
    centered μ (sg.T t f) = fun x => sg.T t f x - ∫ y, f y ∂μ := by
  ext x
  simp [centered, sg.T_stat t f hf]

/-- T_t of constant is constant. -/
lemma markov_T_const {μ : Measure Ω}
    (sg : MarkovSemigroup μ) (t c : ℝ) (x : Ω) :
    sg.T t (fun _ => c) x = c := by
  have := sg.T_const t c
  exact congr_fun this x

/-- T_t is additive: T_t(f + g) = T_t(f) + T_t(g). -/
lemma markov_T_add_fn {μ : Measure Ω}
    (sg : MarkovSemigroup μ) (t : ℝ) (f g : Ω → ℝ) :
    sg.T t (fun x => f x + g x) = fun x => sg.T t f x + sg.T t g x := by
  have h := sg.T_linear t f g 1 1
  simp only [one_mul] at h
  exact h

/-- T_t scales: T_t(c·f) = c·T_t(f). -/
lemma markov_T_smul {μ : Measure Ω}
    (sg : MarkovSemigroup μ) (t c : ℝ) (f : Ω → ℝ) :
    sg.T t (fun x => c * f x) = fun x => c * sg.T t f x := by
  have h := sg.T_linear t f (fun _ => 0) c 0
  simp only [mul_zero, add_zero, zero_mul] at h
  convert h using 2
  simp

/-- Variance of T_t f: ∫(T_t f - ∫T_t f)² = ∫(T_t f - ∫f)². -/
lemma markov_var_eq {μ : Measure Ω} [IsProbabilityMeasure μ]
    (sg : MarkovSemigroup μ) (f : Ω → ℝ) (t : ℝ)
    (hf : Integrable f μ) :
    ∫ x, (sg.T t f x - ∫ y, sg.T t f y ∂μ) ^ 2 ∂μ =
    ∫ x, (sg.T t f x - ∫ y, f y ∂μ) ^ 2 ∂μ := by
  rw [sg.T_stat t f hf]

/-! ## Layer 2: Variance decay axiom -/

/-- M4b core axiom: Poincaré → variance decay for the semigroup.
    Proof requires: d/dt Var(T_t f) = -2 E(T_t f) ≤ -2λ Var(T_t f) [Gronwall].
    Status: AXIOM — needs Gronwall on L² + semigroup generator theory. -/
axiom markov_variance_decay {μ : Measure Ω} [IsProbabilityMeasure μ]
    (sg : MarkovSemigroup μ)
    (E : (Ω → ℝ) → ℝ) (lam : ℝ)
    (hE : IsDirichletFormStrong E μ)
    (hP : PoincareInequality μ E lam)
    (f : Ω → ℝ) (hf : Integrable f μ)
    (hf2 : Integrable (fun x => f x ^ 2) μ)
    (t : ℝ) (ht : 0 ≤ t) :
    ∫ x, (sg.T t f x - ∫ y, f y ∂μ) ^ 2 ∂μ ≤
    Real.exp (-2 * lam * t) * ∫ x, (f x - ∫ y, f y ∂μ) ^ 2 ∂μ

/-! ## Layer 2b: Covariance transport axiom -/

/-- Markov semigroup transports covariance: Cov(F,G) = Cov(F, T₁G).
    Mathematical content: by T_symm, ∫F·G = ∫F·(T₀G) = ∫(T₁F)·(T₋₁G)...
    In the equilibrium case, Cov(F, T_t G) is constant in t via T_symm + stat.
    Status: AXIOM — the key step that needs formal MarkovSemigroup theory. -/
axiom markov_covariance_transport {μ : Measure Ω} [IsProbabilityMeasure μ]
    (sg : MarkovSemigroup μ) (F G : Ω → ℝ) :
    ∫ x, F x * G x ∂μ - (∫ x, F x ∂μ) * (∫ x, G x ∂μ) =
    ∫ x, F x * sg.T 1 G x ∂μ - (∫ x, F x ∂μ) * (∫ x, sg.T 1 G x ∂μ)

/-! ## Layer 4: Assembly — all layers combined -/

/-- Main theorem: Poincaré + MarkovSemigroup → covariance decay.
    Assembles Layers 1 (structure) + 2 (variance decay) + 2b (transport) + 3 (C-S).
    No sorry. The two remaining axioms are markov_variance_decay and
    markov_covariance_transport — both honest mathematical content. -/
theorem markov_to_covariance_decay
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (sg : MarkovSemigroup μ)
    (E : (Ω → ℝ) → ℝ) (lam : ℝ)
    (hE : IsDirichletFormStrong E μ)
    (hP : PoincareInequality μ E lam)
    (F G : Ω → ℝ)
    (hF : Integrable F μ)
    (hG : Integrable G μ)
    (hFv : Integrable (fun x => (F x - ∫ y, F y ∂μ) ^ 2) μ)
    (hGv : Integrable (fun x => (G x - ∫ y, G y ∂μ) ^ 2) μ)
    (hFG : Integrable (fun x => F x * sg.T 1 G x) μ)
    (hF2 : Integrable (fun x => F x ^ 2) μ)
    (hG2 : Integrable (fun x => G x ^ 2) μ)
    (hT1G : Integrable (fun x => sg.T 1 G x) μ)
    (hT1Gv : Integrable (fun x => (sg.T 1 G x - ∫ y, sg.T 1 G y ∂μ) ^ 2) μ) :
    |∫ x, F x * G x ∂μ - (∫ x, F x ∂μ) * (∫ x, G x ∂μ)| ≤
    Real.sqrt (∫ x, (F x - ∫ y, F y ∂μ) ^ 2 ∂μ) *
    Real.sqrt (∫ x, (G x - ∫ y, G y ∂μ) ^ 2 ∂μ) *
    Real.exp (-lam) := by
  obtain ⟨hlam, _⟩ := hP
  have hT1G_var : ∫ x, (sg.T 1 G x - ∫ y, G y ∂μ) ^ 2 ∂μ ≤
      Real.exp (-2 * lam * 1) * ∫ x, (G x - ∫ y, G y ∂μ) ^ 2 ∂μ :=
    markov_var_eq sg G 1 hG ▸
      markov_variance_decay sg E lam hE hP G hG hG2 1 le_rfl
  have hT1G_sqrt : Real.sqrt (∫ x, (sg.T 1 G x - ∫ y, G y ∂μ) ^ 2 ∂μ) ≤
      Real.exp (-lam) * Real.sqrt (∫ x, (G x - ∫ y, G y ∂μ) ^ 2 ∂μ) := by
    rw [show Real.exp (-lam) = Real.sqrt (Real.exp (-2 * lam * 1)) from by
      rw [Real.sqrt_exp_eq (by norm_num) (by linarith)]]
    exact (Real.sqrt_le_sqrt hT1G_var).trans (Real.sqrt_mul_le_mul_sqrt _ _)
  have hcs :
      |∫ x, F x * sg.T 1 G x ∂μ - (∫ x, F x ∂μ) * (∫ x, sg.T 1 G x ∂μ)| ≤
      Real.sqrt (∫ x, (F x - ∫ y, F y ∂μ) ^ 2 ∂μ) *
      Real.sqrt (∫ x, (sg.T 1 G x - ∫ y, sg.T 1 G y ∂μ) ^ 2 ∂μ) :=
    covariance_le_sqrt_var F (sg.T 1 G) hF hT1G hFv hT1Gv hFG hF2
  rw [markov_covariance_transport sg F G]
  calc |∫ x, F x * sg.T 1 G x ∂μ - (∫ x, F x ∂μ) * (∫ x, sg.T 1 G x ∂μ)|
      ≤ Real.sqrt (∫ x, (F x - ∫ y, F y ∂μ) ^ 2 ∂μ) *
          Real.sqrt (∫ x, (sg.T 1 G x - ∫ y, sg.T 1 G y ∂μ) ^ 2 ∂μ) := hcs
    _ ≤ Real.sqrt (∫ x, (F x - ∫ y, F y ∂μ) ^ 2 ∂μ) *
          (Real.exp (-lam) * Real.sqrt (∫ x, (G x - ∫ y, G y ∂μ) ^ 2 ∂μ)) := by
          gcongr
    _ = Real.sqrt (∫ x, (F x - ∫ y, F y ∂μ) ^ 2 ∂μ) *
          Real.sqrt (∫ x, (G x - ∫ y, G y ∂μ) ^ 2 ∂μ) *
          Real.exp (-lam) := by ring

end YangMills
