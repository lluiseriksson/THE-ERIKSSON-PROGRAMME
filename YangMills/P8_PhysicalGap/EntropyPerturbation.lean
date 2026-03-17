import Mathlib
set_option linter.unusedSectionVars false

namespace YangMills
open MeasureTheory Real Filter Set

variable {Ω : Type*} [MeasurableSpace Ω]

lemma integral_one_add_mul_sq
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (u : Ω → ℝ) (t : ℝ)
    (hu1 : Integrable u μ) (hu2 : Integrable (fun x => u x ^ 2) μ)
    (hcenter : ∫ x, u x ∂μ = 0) :
    ∫ x, (1 + t * u x) ^ 2 ∂μ = 1 + t ^ 2 * ∫ x, u x ^ 2 ∂μ := by
  have h1 : Integrable (fun _ : Ω => (1 : ℝ)) μ := integrable_const 1
  have h2 : Integrable (fun x => 2 * t * u x) μ := hu1.const_mul (2 * t)
  have h3 : Integrable (fun x => t ^ 2 * u x ^ 2) μ := hu2.const_mul (t ^ 2)
  have h12 : Integrable (fun x => 1 + 2 * t * u x) μ := h1.add h2
  have heq : (fun x => (1 + t * u x) ^ 2) =
      fun x => (1 + 2 * t * u x) + t ^ 2 * u x ^ 2 := by ext x; ring
  rw [heq, integral_add h12 h3, integral_add h1 h2]
  have hu2_eq : (fun x => 2 * t * u x) = fun x => (2 * t) * u x := by ext; ring
  have hu3_eq : (fun x => t ^ 2 * u x ^ 2) = fun x => (t ^ 2) * u x ^ 2 := by ext; ring
  rw [hu2_eq, hu3_eq, integral_const_mul, integral_const_mul, hcenter]
  have hc1 : ∫ x, (1:ℝ) ∂μ = 1 := by
    rw [integral_const, smul_eq_mul]
    change (μ Set.univ).toReal * 1 = 1
    rw [measure_univ, ENNReal.toReal_one, one_mul]
  rw [hc1]; ring

lemma pos_of_small_t {u : Ω → ℝ} {M : ℝ} (hMpos : 0 < M)
    (hM : ∀ x, |u x| ≤ M) {t : ℝ} (ht : |t| < 1 / (2 * M)) (x : Ω) :
    0 < 1 + t * u x := by
  have h1 : |t * u x| < 1 / 2 := by
    calc |t * u x| = |t| * |u x| := abs_mul t (u x)
      _ ≤ |t| * M := mul_le_mul_of_nonneg_left (hM x) (abs_nonneg t)
      _ < 1 / (2 * M) * M := mul_lt_mul_of_pos_right ht hMpos
      _ = 1 / 2 := by field_simp
  linarith [neg_abs_le (t * u x)]

lemma log_taylor_bound {y : ℝ} (hy : |y| ≤ 1/2) :
    |Real.log (1 + y) - y + y ^ 2 / 2| ≤ 2 * |y| ^ 3 := by
  have hylt : |-y| < 1 := by simp [abs_neg]; linarith
  have hseries := Real.abs_log_sub_add_sum_range_le hylt 2
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hseries
  rw [show Real.log (1 - -y) = Real.log (1 + y) from by ring_nf,
      show |-y| ^ (2 + 1) = |-y| ^ 3 from by norm_num] at hseries
  have hkey : |Real.log (1 + y) - y + y ^ 2 / 2| ≤ |-y| ^ 3 / (1 - |-y|) := by
    convert hseries using 1; congr 1; push_cast; ring
  have hfrac : |-y| ^ 3 / (1 - |-y|) ≤ 2 * |y| ^ 3 := by
    simp only [abs_neg]
    have hdist : 1 / 2 ≤ 1 - |y| := by linarith
    have hpos : 0 < 1 - |y| := by linarith
    rw [div_le_iff₀ hpos]
    nlinarith [sq_nonneg (|y|), pow_nonneg (abs_nonneg y) 3]
  linarith

lemma sq_log_expansion_bound {h : ℝ} (hh : |h| ≤ 1/2) :
    |(1 + h) ^ 2 * (2 * Real.log (1 + h)) - 2 * h - 3 * h ^ 2| ≤ 14 * |h| ^ 3 := by
  let E := Real.log (1 + h) - h + h ^ 2 / 2
  have hE : |E| ≤ 2 * |h| ^ 3 := log_taylor_bound hh
  have hlogeq : Real.log (1 + h) = h - h ^ 2 / 2 + E := by dsimp [E]; linarith
  rw [show (1 + h) ^ 2 * (2 * Real.log (1 + h)) - 2 * h - 3 * h ^ 2 =
      (2 + 4*h + 2*h^2) * E - h^4 from by rw [hlogeq]; ring]
  have hcoeff : |2 + 4*h + 2*h^2| ≤ 6 := by
    rw [abs_le]; constructor <;> nlinarith [neg_abs_le h, le_abs_self h, sq_nonneg h]
  have h_h4 : |h|^4 ≤ (1/2) * |h|^3 := by
    nlinarith [abs_nonneg h, sq_nonneg h, pow_nonneg (abs_nonneg h) 3]
  have h_triangle : |(2 + 4*h + 2*h^2) * E - h^4| ≤
      |(2 + 4*h + 2*h^2) * E| + |h|^4 := by
    calc |(2 + 4*h + 2*h^2) * E - h^4|
        = |(2 + 4*h + 2*h^2) * E + (-(h^4))| := by ring_nf
      _ ≤ |(2 + 4*h + 2*h^2) * E| + |-(h^4)| := abs_add_le _ _
      _ = |(2 + 4*h + 2*h^2) * E| + |h|^4 := by rw [abs_neg, abs_pow]
  calc |(2 + 4*h + 2*h^2) * E - h^4|
      ≤ |(2 + 4*h + 2*h^2) * E| + |h|^4 := h_triangle
    _ = |2 + 4*h + 2*h^2| * |E| + |h|^4 := by rw [abs_mul]
    _ ≤ 6 * (2 * |h|^3) + (1/2) * |h|^3 := by nlinarith [abs_nonneg E]
    _ ≤ 14 * |h|^3 := by nlinarith [pow_nonneg (abs_nonneg h) 3]

/-- The limit (1+s)log(1+s)/s → 1 as s→0.
    Sorry: HasDerivAt.tendsto_slope composition in nhdsWithin. -/
lemma norm_term_tendsto (c : ℝ) :
    Tendsto (fun t : ℝ => (1 + t ^ 2 * c) * Real.log (1 + t ^ 2 * c) / t ^ 2)
      (nhdsWithin 0 {0}ᶜ) (nhds c) := by
  sorry

/-- Entropy perturbation formula: Ent_μ((1+tu)²)/t² → 2·Var_μ(u) as t→0.

Sorry: main limit argument (integrand manipulation + squeeze).
Helper lemmas above are proved. -/
theorem entropy_perturbation_limit_proved
    (μ : Measure Ω) [IsProbabilityMeasure μ] (u : Ω → ℝ)
    (hu : Measurable u) (hbdd : ∃ M > 0, ∀ x, |u x| ≤ M)
    (hcenter : ∫ x, u x ∂μ = 0)
    (hu2 : Integrable (fun x => u x ^ 2) μ) :
    Filter.Tendsto
      (fun t : ℝ => (∫ x, (1 + t * u x) ^ 2 * log ((1 + t * u x) ^ 2) ∂μ -
        (∫ x, (1 + t * u x) ^ 2 ∂μ) * log (∫ x, (1 + t * u x) ^ 2 ∂μ)) / t ^ 2)
      (nhdsWithin 0 {0}ᶜ)
      (nhds (2 * ∫ x, u x ^ 2 ∂μ)) := by
  obtain ⟨M, hMpos, hM⟩ := hbdd
  have hu1 : Integrable u μ := by
    apply Integrable.mono' (integrable_const M) hu.aestronglyMeasurable
    exact ae_of_all _ fun x => by
      simp only [Real.norm_eq_abs]; exact hM x
  set c := ∫ x, u x ^ 2 ∂μ
  have hnorm_id : ∀ t : ℝ, ∫ x, (1 + t * u x) ^ 2 ∂μ = 1 + t ^ 2 * c :=
    fun t => integral_one_add_mul_sq μ u t hu1 hu2 hcenter
  sorry

end YangMills
