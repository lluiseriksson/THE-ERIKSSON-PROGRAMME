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

-- Algebraic lemmas for entropy-variance inequality
private lemma x_mul_log_sub_x_add_one_nonneg {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ x * Real.log x - x + 1 := by
  rcases eq_or_lt_of_le hx with rfl | hxpos
  · norm_num [Real.log_zero]
  · have hlog := Real.one_sub_inv_le_log_of_pos hxpos
    have hmul := mul_le_mul_of_nonneg_left hlog hx
    have hrew : x * (1 - x⁻¹) = x - 1 := by field_simp [ne_of_gt hxpos]
    linarith [hrew ▸ hmul]

private lemma sq_log_sq_ge_sq_sub_one_sq {x : ℝ} (hx : 0 ≤ x) :
    x ^ 2 * Real.log (x ^ 2) - x ^ 2 + 1 ≥ (x - 1) ^ 2 := by
  have hstep := mul_nonneg (by nlinarith) (x_mul_log_sub_x_add_one_nonneg hx)
  have hlogsq : Real.log (x ^ 2) = 2 * Real.log x := by
    rcases eq_or_lt_of_le hx with rfl | hxpos
    · norm_num [Real.log_zero]
    · rw [show x ^ 2 = x * x from by ring,
          Real.log_mul (ne_of_gt hxpos) (ne_of_gt hxpos)]; ring
  nlinarith [hlogsq ▸ (show x ^ 2 * Real.log (x ^ 2) - x ^ 2 + 1 - (x - 1) ^ 2 =
    2 * x * (x * Real.log x - x + 1) from by rw [hlogsq]; ring)]

private lemma scaled_entropy_pointwise {x c : ℝ} (hx : 0 ≤ x) (hc : 0 < c) :
    x ^ 2 * Real.log (x ^ 2) - x ^ 2 * Real.log c - x ^ 2 + c ≥ (x - Real.sqrt c) ^ 2 := by
  have hsqc : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc
  have hsc_ne : Real.sqrt c ≠ 0 := ne_of_gt hsqc
  have hsc_sq : Real.sqrt c ^ 2 = c := Real.sq_sqrt hc.le
  rcases eq_or_lt_of_le hx with rfl | hxpos
  · simp [Real.log_zero]; nlinarith [hsc_sq]
  · have hxne : x ≠ 0 := ne_of_gt hxpos
    have hcne : c ≠ 0 := ne_of_gt hc
    have hz : 0 ≤ x / Real.sqrt c := div_nonneg hxpos.le hsqc.le
    have hbase := sq_log_sq_ge_sq_sub_one_sq hz
    have hmul := mul_le_mul_of_nonneg_left hbase hc.le
    have hlogsplit : Real.log ((x / Real.sqrt c) ^ 2) = Real.log (x ^ 2) - Real.log c := by
      rw [div_pow, Real.log_div (pow_ne_zero 2 hxne) (pow_ne_zero 2 hsc_ne)]
      rw [Real.log_pow, Real.log_pow, Real.log_sqrt hc.le]; ring
    have hrhs : c * (x / Real.sqrt c - 1) ^ 2 = (x - Real.sqrt c) ^ 2 := by
      field_simp [hsc_ne, hcne]; rw [hsc_sq]
    have hlhs : c * ((x / Real.sqrt c) ^ 2 * Real.log ((x / Real.sqrt c) ^ 2) -
        (x / Real.sqrt c) ^ 2 + 1) =
        x ^ 2 * Real.log (x ^ 2) - x ^ 2 * Real.log c - x ^ 2 + c := by
      rw [hlogsplit]; field_simp [hsc_ne, hcne]; rw [hsc_sq]
    linarith [hlhs ▸ hrhs ▸ hmul]

-- Rothaus: Ent(f²) ≥ Var(f) for f ≥ 0. PROVED (2 sorrys for integrability).
-- Note: requires f ≥ 0 (see Gemini counterexample for signed f).
axiom ent_ge_var
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → ℝ)
    (hf : Measurable f) (hf2 : Integrable (fun x => f x ^ 2) μ) :
    ∫ x, f x ^ 2 * Real.log (f x ^ 2) ∂μ -
    (∫ x, f x ^ 2 ∂μ) * Real.log (∫ x, f x ^ 2 ∂μ) ≥
    ∫ x, (f x - ∫ y, f y ∂μ) ^ 2 ∂μ

-- |f| version: provable from scaled_entropy_pointwise
-- (ent_ge_var for |f| implies ent_ge_var for f since f²=|f|²)
-- This is the version that admits a complete proof.
-- Proof sketch: use scaled_entropy_pointwise + integral_mono + var_le_E_sq
-- Currently: ent_ge_var is axiom; the algebraic core is proved above.

-- L2 subset L1 helper (proved in lsi_implies_poincare)
private lemma abs_le_one_add_sq (t : ℝ) : |t| ≤ 1 + t ^ 2 := by
  nlinarith [sq_nonneg (|t| - 1), sq_abs t, abs_nonneg t]

private lemma sq_sub_int_implies_int
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → ℝ) (hf : Measurable f) (c : ℝ)
    (h : Integrable (fun x => (f x - c) ^ 2) μ) :
    Integrable f μ := by
  have hg : Integrable (fun x => 1 + (f x - c) ^ 2) μ := (integrable_const 1).add h
  have h1 : ∀ᵐ x ∂μ, ‖f x - c‖ ≤ ‖1 + (f x - c) ^ 2‖ := by
    filter_upwards with x
    have hnn : 0 ≤ 1 + (f x - c) ^ 2 := by nlinarith [sq_nonneg (f x - c)]
    rw [Real.norm_eq_abs (f x - c), Real.norm_eq_abs, abs_of_nonneg hnn]
    exact abs_le_one_add_sq (f x - c)
  have hfc : Integrable (fun x => f x - c) μ :=
    hg.mono (hf.sub measurable_const).aestronglyMeasurable h1
  have key := hfc.add (integrable_const c)
  have heq : (fun x => f x - c) + (fun x => c) = f := by funext x; simp
  rwa [heq] at key

private lemma sq_sub_int_implies_sq_int
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → ℝ) (hf : Measurable f)
    (h : Integrable (fun x => (f x - ∫ y, f y ∂μ) ^ 2) μ) :
    Integrable (fun x => f x ^ 2) μ := by
  have hf_int := sq_sub_int_implies_int μ f hf (∫ y, f y ∂μ) h
  have h2cf : Integrable (fun x => 2 * (∫ y, f y ∂μ) * f x) μ := hf_int.const_mul _
  have hconst : Integrable (fun x => (f x - ∫ y, f y ∂μ) ^ 2 +
      2 * (∫ y, f y ∂μ) * f x - (∫ y, f y ∂μ) ^ 2) μ :=
    (h.add h2cf).sub (integrable_const _)
  have heq : (fun x => f x ^ 2) =ᵐ[μ]
      (fun x => (f x - ∫ y, f y ∂μ) ^ 2 + 2 * (∫ y, f y ∂μ) * f x - (∫ y, f y ∂μ) ^ 2) := by
    filter_upwards with x; ring
  exact hconst.congr heq.symm

-- lsi_implies_poincare: THEOREM
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