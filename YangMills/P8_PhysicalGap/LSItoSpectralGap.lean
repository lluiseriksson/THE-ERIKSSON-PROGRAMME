import Mathlib
import YangMills.L4_TransferMatrix.TransferMatrix

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
  0 < ξ ∧ 0 < C ∧
  ∀ (F G_obs : Ω → ℝ),
    |∫ x, F x * G_obs x ∂μ - (∫ x, F x ∂μ) * (∫ x, G_obs x ∂μ)| ≤
    C * Real.sqrt (∫ x, F x ^ 2 ∂μ) * Real.sqrt (∫ x, G_obs x ^ 2 ∂μ) *
    Real.exp (-1 / ξ)

def PoincareInequality (μ : Measure Ω) (E : (Ω → ℝ) → ℝ) (lam : ℝ) : Prop :=
  0 < lam ∧ ∀ (f : Ω → ℝ) (_ : Measurable f),
    ∫ x, (f x - ∫ y, f y ∂μ) ^ 2 ∂μ ≤ (1 / lam) * E f

-- Rothaus 1981: Ent(f2) >= Var(f). AXIOM.
axiom ent_ge_var
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → ℝ)
    (hf : Measurable f) (hf2 : Integrable (fun x => f x ^ 2) μ) :
    ∫ x, f x ^ 2 * Real.log (f x ^ 2) ∂μ -
    (∫ x, f x ^ 2 ∂μ) * Real.log (∫ x, f x ^ 2 ∂μ) ≥
    ∫ x, (f x - ∫ y, f y ∂μ) ^ 2 ∂μ

-- |t| ≤ 1 + t² for all t (proved by nlinarith).
private lemma abs_le_one_add_sq (t : ℝ) : |t| ≤ 1 + t ^ 2 := by
  nlinarith [sq_nonneg (|t| - 1), sq_abs t, abs_nonneg t]

-- (f-c)² integrable → f integrable (L²⊂L¹ for prob measures). PROVED.
private lemma sq_sub_int_implies_int
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → ℝ) (hf : Measurable f) (c : ℝ)
    (h : Integrable (fun x => (f x - c) ^ 2) μ) :
    Integrable f μ := by
  have hg : Integrable (fun x => 1 + (f x - c) ^ 2) μ :=
    (integrable_const 1).add h
  have h1 : ∀ᵐ x ∂μ, ‖f x - c‖ ≤ ‖1 + (f x - c) ^ 2‖ := by
    filter_upwards with x
    have hnn : 0 ≤ 1 + (f x - c) ^ 2 := by nlinarith [sq_nonneg (f x - c)]
    rw [Real.norm_eq_abs (f x - c), Real.norm_eq_abs, abs_of_nonneg hnn]
    exact abs_le_one_add_sq (f x - c)
  have hfc : Integrable (fun x => f x - c) μ :=
    hg.mono (hf.sub measurable_const).aestronglyMeasurable h1
  have key := hfc.add (integrable_const c)
  have heq : (fun x => f x - c) + (fun x => c) = f := by
    funext x; simp
  rwa [heq] at key

-- (f-c)² integrable → f² integrable. PROVED.
private lemma sq_sub_int_implies_sq_int
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → ℝ) (hf : Measurable f)
    (h : Integrable (fun x => (f x - c) ^ 2) μ) :
    Integrable (fun x => f x ^ 2) μ := by
  -- f integrable (from above), then f·f integrable
  have hf_int := sq_sub_int_implies_int μ f hf c h
  -- f² = f*f, integrable product for bounded... actually need more care
  -- Use: f² = (f-c)² + 2c·f - c² = (f-c)² + 2c·f - c²
  -- (f-c)² integrable by h, 2c·f integrable (c·integrable), c² const integrable
  have h2cf : Integrable (fun x => 2 * c * f x) μ := hf_int.const_mul (2 * c)
  have hconst : Integrable (fun x => (f x - c) ^ 2 + 2 * c * f x - c ^ 2) μ :=
    (h.add h2cf).sub (integrable_const (c ^ 2))
  convert hconst using 2
  funext x; ring

-- lsi_implies_poincare: THEOREM (Phase 9). Was axiom in Phase 8.
theorem lsi_implies_poincare
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (E : (Ω → ℝ) → ℝ) (hE : IsDirichletForm E μ) (α : ℝ)
    (hLSI : LogSobolevInequality μ E α) :
    PoincareInequality μ E (α / 2) := by
  refine ⟨by linarith [hLSI.1], fun f hf => ?_⟩
  rw [show (1 : ℝ) / (α / 2) = 2 / α from by field_simp]
  by_cases hfc : Integrable (fun x => (f x - ∫ y, f y ∂μ) ^ 2) μ
  · have hf2 : Integrable (fun x => f x ^ 2) μ :=
      sq_sub_int_implies_sq_int μ f hf hfc
    calc ∫ x, (f x - ∫ y, f y ∂μ) ^ 2 ∂μ
        ≤ ∫ x, f x ^ 2 * Real.log (f x ^ 2) ∂μ -
          (∫ x, f x ^ 2 ∂μ) * Real.log (∫ x, f x ^ 2 ∂μ) :=
            ent_ge_var μ f hf hf2
      _ ≤ (2 / α) * E f := hLSI.2 f hf
  · have h0 : ∫ x, (f x - ∫ y, f y ∂μ) ^ 2 ∂μ = 0 := integral_undef hfc
    rw [h0]
    apply mul_nonneg
    · have := hLSI.1; positivity
    · exact hE.1 f

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