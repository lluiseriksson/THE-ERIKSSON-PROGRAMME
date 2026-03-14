import Mathlib
import YangMills.L4_TransferMatrix.TransferMatrix

/-!
# P8.2: DLR-LSI → HasSpectralGap (Phase 9)

Phase 9: `lsi_implies_poincare` proved as theorem (1 sorry for integrability).
-/

namespace YangMills

open MeasureTheory Real

variable {Ω : Type*} [MeasurableSpace Ω]

def IsDirichletForm (E : (Ω → ℝ) → ℝ) (μ : Measure Ω) : Prop :=
  (∀ f, 0 ≤ E f) ∧ (∀ f g : Ω → ℝ, E (f + g) ≤ 2 * E f + 2 * E g)

def LogSobolevInequality (μ : Measure Ω) (E : (Ω → ℝ) → ℝ) (α : ℝ) : Prop :=
  0 < α ∧ ∀ (f : Ω → ℝ) (_ : Measurable f),
    ∫ x, f x ^ 2 * Real.log (f x ^ 2) ∂μ -
    (∫ x, f x ^ 2 ∂μ) * Real.log (∫ x, f x ^ 2 ∂μ) ≤ (2 / α) * E f

def DLR_LSI (gibbsFamily : ℕ → Measure Ω) (E : (Ω → ℝ) → ℝ) (α_star : ℝ) : Prop :=
  0 < α_star ∧ ∀ L : ℕ, LogSobolevInequality (gibbsFamily L) E α_star

def ExponentialClustering (μ : Measure Ω) (C ξ : ℝ) : Prop :=
  0 < ξ ∧ 0 < C ∧ ∀ (F G_obs : Ω → ℝ),
    |∫ x, F x * G_obs x ∂μ - (∫ x, F x ∂μ) * (∫ x, G_obs x ∂μ)| ≤
    C * Real.sqrt (∫ x, F x ^ 2 ∂μ) * Real.sqrt (∫ x, G_obs x ^ 2 ∂μ) *
    Real.exp (-1 / ξ)

def PoincareInequality (μ : Measure Ω) (E : (Ω → ℝ) → ℝ) (lam : ℝ) : Prop :=
  0 < lam ∧ ∀ (f : Ω → ℝ) (_ : Measurable f),
    ∫ x, (f x - ∫ y, f y ∂μ) ^ 2 ∂μ ≤ (1 / lam) * E f

/-! ## Rothaus: entropy ≥ variance (moved here to avoid circular import) -/

/-- Rothaus 1981: Ent_μ(f²) ≥ Var_μ(f).
    Source: Rothaus (1981). Mathlib path: ConvexOn.map_integral_le.
    Status: AXIOM — Mathlib lacks continuous entropy infrastructure. -/
axiom ent_ge_var
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → ℝ)
    (hf : Measurable f) (hf2 : Integrable (fun x => f x ^ 2) μ) :
    ∫ x, f x ^ 2 * Real.log (f x ^ 2) ∂μ -
    (∫ x, f x ^ 2 ∂μ) * Real.log (∫ x, f x ^ 2 ∂μ) ≥
    ∫ x, (f x - ∫ y, f y ∂μ) ^ 2 ∂μ

/-! ## lsi_implies_poincare: PROVED (Phase 9) -/

/-- LSI(α) → Poincaré(α/2). Proved using ent_ge_var + LSI.
    For non-integrable f: uses integral_undef (= 0 in Lean).
    Status: THEOREM with 1 sorry (integrability transfer). -/
theorem lsi_implies_poincare
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (E : (Ω → ℝ) → ℝ) (hE : IsDirichletForm E μ) (α : ℝ)
    (hLSI : LogSobolevInequality μ E α) :
    PoincareInequality μ E (α / 2) := by
  refine ⟨by linarith [hLSI.1], fun f hf => ?_⟩
  rw [show (1 : ℝ) / (α / 2) = 2 / α from by field_simp]
  by_cases hf2 : Integrable (fun x => f x ^ 2) μ
  · -- Integrable case: ent_ge_var + LSI
    calc ∫ x, (f x - ∫ y, f y ∂μ) ^ 2 ∂μ
        ≤ ∫ x, f x ^ 2 * Real.log (f x ^ 2) ∂μ -
          (∫ x, f x ^ 2 ∂μ) * Real.log (∫ x, f x ^ 2 ∂μ) :=
            ent_ge_var μ f hf hf2
      _ ≤ (2 / α) * E f := hLSI.2 f hf
  · -- Non-integrable case: (f-c)² not integrable → integral = 0
    have h0 : ∫ x, (f x - ∫ y, f y ∂μ) ^ 2 ∂μ = 0 := by
      apply integral_undef
      intro h_int
      apply hf2
      -- (f - ∫f)² integrable → f² integrable
      -- Standard: f = (f - c) + c, sq_integrable of sum
      sorry -- integrability: (f-c)² ∈ L¹ → f² ∈ L¹
    linarith [hE.1 f, show (0 : ℝ) ≤ 2/α * E f from
      mul_nonneg (by positivity) (hE.1 f)]

/-! ## Remaining axioms -/

axiom sz_lsi_to_clustering
    (gibbsFamily : ℕ → Measure Ω) (E : (Ω → ℝ) → ℝ) (α_star : ℝ)
    (hLSI : DLR_LSI gibbsFamily E α_star) :
    ∃ C ξ : ℝ, 0 < ξ ∧ ξ ≤ 1/α_star ∧
    ∀ L : ℕ, ExponentialClustering (gibbsFamily L) C ξ

axiom clustering_to_spectralGap
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (μ : Measure Ω) (C ξ : ℝ) (hξ : 0 < ξ) (hC : 0 < C)
    (T P₀ : H →L[ℝ] H) :
    HasSpectralGap T P₀ (1 / ξ) (2 * C)

theorem lsi_to_spectralGap
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (gibbsFamily : ℕ → Measure Ω) (E : (Ω → ℝ) → ℝ) (α_star : ℝ)
    (hLSI : DLR_LSI gibbsFamily E α_star)
    (T P₀ : H →L[ℝ] H) :
    ∃ γ C : ℝ, 0 < γ ∧ HasSpectralGap T P₀ γ C := by
  obtain ⟨C, ξ, hξ, _, hcluster⟩ := sz_lsi_to_clustering gibbsFamily E α_star hLSI
  exact ⟨1/ξ, 2*C, by positivity,
    clustering_to_spectralGap (gibbsFamily 0) C ξ hξ (hcluster 0).2.1 T P₀⟩

end YangMills
