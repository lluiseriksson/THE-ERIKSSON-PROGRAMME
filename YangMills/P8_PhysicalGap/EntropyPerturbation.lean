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

lemma norm_term_bound {y : ℝ} (hy : |y| ≤ 1/2) :
    |(1 + y) * Real.log (1 + y) - y| ≤ 4 * y ^ 2 := by
  let E := Real.log (1 + y) - y + y ^ 2 / 2
  have hE : |E| ≤ 2 * |y| ^ 3 := log_taylor_bound hy
  have hlog : Real.log (1 + y) = y - y ^ 2 / 2 + E := by dsimp [E]; linarith
  have heq : (1 + y) * Real.log (1 + y) - y = y ^ 2 / 2 - y ^ 3 / 2 + (1 + y) * E := by
    rw [hlog]; ring
  have htri : |(1 + y) * Real.log (1 + y) - y| ≤ |y ^ 2 / 2 - y ^ 3 / 2| + |(1 + y) * E| := by
    rw [heq]; exact abs_add_le _ _
  have h1 : |y ^ 2 / 2 - y ^ 3 / 2| ≤ |y| ^ 2 := by
    calc |y ^ 2 / 2 - y ^ 3 / 2|
        = |y ^ 2 / 2 + (-y ^ 3 / 2)| := by ring_nf
      _ ≤ |y ^ 2 / 2| + |-y ^ 3 / 2| := abs_add_le _ _
      _ = |y| ^ 2 / 2 + |y| ^ 3 / 2 := by
          rw [abs_div, abs_pow, abs_of_pos (by norm_num : (0:ℝ) < 2),
              abs_div, abs_neg, abs_pow, abs_of_pos (by norm_num : (0:ℝ) < 2)]
      _ ≤ |y| ^ 2 / 2 + |y| ^ 2 / 2 := by
          have h_y_le : |y| ≤ 1 := by linarith
          nlinarith [sq_nonneg (|y|), mul_le_mul_of_nonneg_right h_y_le (sq_nonneg (|y|))]
      _ = |y| ^ 2 := by ring
  have h2 : |(1 + y) * E| ≤ 3 * |y| ^ 2 := by
    have h1y : |1 + y| ≤ 3 / 2 := by
      calc |1 + y| ≤ |(1:ℝ)| + |y| := abs_add_le 1 y
        _ ≤ 1 + 1/2 := by rw [abs_one]; linarith
        _ = 3/2 := by norm_num
    have h_y_le : |y| ≤ 1 := by linarith
    calc |(1 + y) * E| = |1 + y| * |E| := abs_mul _ _
      _ ≤ (3/2) * (2 * |y|^3) := by nlinarith [abs_nonneg E]
      _ = 3 * |y|^3 := by ring
      _ ≤ 3 * |y|^2 := by
          nlinarith [sq_nonneg (|y|), mul_le_mul_of_nonneg_right h_y_le (sq_nonneg (|y|))]
  calc |(1 + y) * Real.log (1 + y) - y|
      ≤ |y ^ 2 / 2 - y ^ 3 / 2| + |(1 + y) * E| := htri
    _ ≤ |y|^2 + 3 * |y|^2 := add_le_add h1 h2
    _ = 4 * |y|^2 := by ring
    _ = 4 * y^2 := by rw [sq_abs]

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

lemma R_bound {u : Ω → ℝ} {M : ℝ} (hM : ∀ x, |u x| ≤ M) (t : ℝ) (x : Ω)
    (htux : |t * u x| ≤ 1/2) :
    |(1 + t * u x)^2 * (2 * Real.log (1 + t * u x)) - 2 * (t * u x) - 3 * (t * u x)^2|
      ≤ (14 * M * |t|^3) * u x ^ 2 := by
  have hux : |u x| ≤ M := hM x
  have h1 : |u x|^3 = |u x| * u x^2 := by
    calc |u x|^3 = |u x| * |u x|^2 := by ring
      _ = |u x| * u x^2 := by rw [sq_abs]
  calc |(1 + t * u x)^2 * (2 * Real.log (1 + t * u x)) - 2 * (t * u x) - 3 * (t * u x)^2|
      ≤ 14 * |t * u x|^3 := sq_log_expansion_bound htux
    _ = 14 * (|t|^3 * |u x|^3) := by rw [abs_mul, mul_pow]
    _ = 14 * (|t|^3 * (|u x| * u x^2)) := by rw [h1]
    _ ≤ 14 * (|t|^3 * (M * u x^2)) := by
        nlinarith [pow_nonneg (abs_nonneg t) 3,
                   mul_le_mul_of_nonneg_right hux (sq_nonneg (u x))]
    _ = (14 * M * |t|^3) * u x^2 := by ring

lemma norm_term_tendsto (c : ℝ) :
    Tendsto (fun t : ℝ => (1 + t ^ 2 * c) * Real.log (1 + t ^ 2 * c) / t ^ 2)
      (nhdsWithin 0 {0}ᶜ) (nhds c) := by
  by_cases hc : c = 0
  · simp [hc, tendsto_const_nhds]
  · suffices h : Tendsto (fun t : ℝ => (1 + t^2*c) * Real.log (1 + t^2*c) / t^2 - c)
        (nhdsWithin 0 {0}ᶜ) (nhds 0) by
      have := h.add_const c; simp only [zero_add] at this
      exact this.congr (fun t => by ring)
    have h_t2c : Tendsto (fun t : ℝ => t^2 * c) (nhds 0) (nhds 0) := by
      have h1 : Tendsto (fun t : ℝ => t^2) (nhds 0) (nhds 0) := by
        have h := (continuous_pow 2).tendsto (0:ℝ)
        simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at h; exact h
      have h2 := h1.mul_const c; simp only [zero_mul] at h2; exact h2
    have h_abs : Tendsto (fun t : ℝ => |t^2 * c|) (nhds 0) (nhds 0) := by
      have := h_t2c.abs; simp only [abs_zero] at this; exact this
    have h_small : ∀ᶠ t in nhdsWithin 0 {0}ᶜ, |t^2 * c| ≤ 1/2 := by
      have hev : ∀ᶠ t in nhds 0, |t^2 * c| < 1/2 :=
        h_abs.eventually (Iio_mem_nhds (by norm_num : (0:ℝ) < 1/2))
      exact (hev.filter_mono nhdsWithin_le_nhds).mono (fun _ h => le_of_lt h)
    have h_lim : Tendsto (fun t : ℝ => 4 * c^2 * t^2) (nhdsWithin 0 {0}ᶜ) (nhds 0) := by
      have h1 : Tendsto (fun t : ℝ => t^2) (nhds 0) (nhds 0) := by
        have h := (continuous_pow 2).tendsto (0:ℝ)
        simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at h; exact h
      have h2 := (tendsto_nhdsWithin_of_tendsto_nhds (s := ({0} : Set ℝ)ᶜ) h1).const_mul (4 * c^2)
      simp only [mul_zero] at h2; exact h2.congr (fun t => by ring)
    -- build ∀ᶠ bound on |f t - c|
    have h_bound_ev : ∀ᶠ t in nhdsWithin 0 {0}ᶜ,
        |(1 + t^2 * c) * Real.log (1 + t^2 * c) / t^2 - c| ≤ 4 * c^2 * t^2 := by
      filter_upwards [h_small, self_mem_nhdsWithin] with t ht_small ht0
      have ht0_ne : t ≠ 0 := Set.mem_compl_singleton_iff.mp ht0
      have ht2pos : 0 < t^2 := sq_pos_of_ne_zero ht0_ne
      have ht2ne : t^2 ≠ 0 := ht2pos.ne'
      have h_eq : (1 + t^2*c) * Real.log (1 + t^2*c) / t^2 - c =
          ((1 + t^2*c) * Real.log (1 + t^2*c) - t^2*c) / t^2 := by
        field_simp [ht0_ne]
      rw [h_eq, abs_div, abs_of_pos ht2pos]
      calc |(1 + t^2*c) * Real.log (1 + t^2*c) - t^2*c| / t^2
          ≤ (4 * (t^2*c)^2) / t^2 :=
              div_le_div_of_nonneg_right (norm_term_bound ht_small) (le_of_lt ht2pos)
        _ = 4 * c^2 * t^2 := by rw [div_eq_iff ht2ne]; ring
    rw [tendsto_zero_iff_norm_tendsto_zero]
    exact squeeze_zero'
      (Filter.Eventually.of_forall fun _ => norm_nonneg _)
      h_bound_ev h_lim

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
  have hu1 : Integrable u μ :=
    Integrable.mono' (integrable_const M) hu.aestronglyMeasurable
      (ae_of_all _ fun x => by simp only [Real.norm_eq_abs]; exact hM x)
  set c := ∫ x, u x ^ 2 ∂μ
  have hnorm_id : ∀ t : ℝ, ∫ x, (1 + t * u x) ^ 2 ∂μ = 1 + t ^ 2 * c :=
    fun t => integral_one_add_mul_sq μ u t hu1 hu2 hcenter
  simp_rw [hnorm_id]
  have h_norm := norm_term_tendsto c
  suffices h_int : Tendsto
      (fun t => (∫ x, (1 + t * u x) ^ 2 * log ((1 + t * u x) ^ 2) ∂μ) / t ^ 2)
      (nhdsWithin 0 {0}ᶜ) (nhds (3 * c)) by
    have h_diff := h_int.sub h_norm
    simp only [show 3 * c - c = 2 * c by ring] at h_diff
    exact h_diff.congr' (eventually_nhdsWithin_of_forall fun t ht => by
      have ht0 : t ≠ 0 := Set.mem_compl_singleton_iff.mp ht
      field_simp [pow_ne_zero 2 ht0])
  have h_abs_t : Tendsto (fun t : ℝ => |t|) (nhdsWithin 0 {0}ᶜ) (nhds 0) := by
    have h := continuous_abs.tendsto (0:ℝ)
    simp only [abs_zero] at h; exact tendsto_nhdsWithin_of_tendsto_nhds h
  have hev_ne : ∀ᶠ t in nhdsWithin (0:ℝ) ({0} : Set ℝ)ᶜ, t ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact Set.mem_compl_singleton_iff.mp ht
  have hev_small : ∀ᶠ t in nhdsWithin 0 {0}ᶜ, ∀ x, |t * u x| ≤ 1/2 := by
    have h0 : Tendsto (fun t : ℝ => |t| * M) (nhdsWithin 0 {0}ᶜ) (nhds 0) := by
      have := h_abs_t.mul_const M; simp only [zero_mul] at this; exact this
    filter_upwards [h0.eventually (Iio_mem_nhds (by norm_num : (0:ℝ) < 1/2))] with t ht x
    calc |t * u x| = |t| * |u x| := abs_mul t (u x)
      _ ≤ |t| * M := mul_le_mul_of_nonneg_left (hM x) (abs_nonneg t)
      _ ≤ 1/2 := le_of_lt ht
  have h_poly : ∀ t : ℝ, t ≠ 0 →
      (∫ x, (2 * (t * u x) + 3 * (t * u x) ^ 2) ∂μ) / t ^ 2 = 3 * c := by
    intro t ht
    rw [show (fun x => 2 * (t * u x) + 3 * (t * u x) ^ 2) =
        fun x => (2 * t) * u x + (3 * t ^ 2) * u x ^ 2 from by ext; ring,
        integral_add (hu1.const_mul _) (hu2.const_mul _),
        integral_const_mul, integral_const_mul, hcenter, mul_zero, zero_add]
    field_simp [pow_ne_zero 2 ht]; ring
  have hR_int_of : ∀ t : ℝ, (∀ x, |t * u x| ≤ 1/2) →
      Integrable (fun x =>
        (1 + t * u x)^2 * (2 * Real.log (1 + t * u x)) - 2 * (t * u x) - 3 * (t * u x)^2) μ := by
    intro t htux
    have htu : Measurable (fun x => t * u x) := hu.const_mul t
    have h1p : Measurable (fun x => 1 + t * u x) := htu.const_add 1
    have hlog : Measurable (fun x => Real.log (1 + t * u x)) := Real.measurable_log.comp h1p
    have h_meas : Measurable (fun x =>
        (1 + t * u x)^2 * (2 * Real.log (1 + t * u x)) - 2 * (t * u x) - 3 * (t * u x)^2) :=
      (((h1p.pow_const 2).mul (hlog.const_mul 2)).sub (htu.const_mul 2)).sub
        ((htu.pow_const 2).const_mul 3)
    exact (hu2.const_mul (14 * M * |t|^3)).mono' h_meas.aestronglyMeasurable
      (ae_of_all _ fun x => by simp only [Real.norm_eq_abs]; exact R_bound hM t x (htux x))
  have h_lim_t : Tendsto (fun t : ℝ => 14 * M * c * |t|) (nhdsWithin 0 {0}ᶜ) (nhds 0) := by
    have := h_abs_t.const_mul (14 * M * c); simp only [mul_zero] at this; exact this
  have h_bound : ∀ᶠ t in nhdsWithin 0 {0}ᶜ,
      ‖(∫ x, ((1 + t * u x)^2 * (2 * Real.log (1 + t * u x)) -
        2 * (t * u x) - 3 * (t * u x)^2) ∂μ) / t^2‖
      ≤ 14 * M * c * |t| := by
    filter_upwards [hev_small, hev_ne] with t htux ht_ne
    have ht2pos : (0:ℝ) < t^2 := sq_pos_of_ne_zero ht_ne
    have ht2ne : t^2 ≠ 0 := ht2pos.ne'
    -- Rewrite norm of division explicitly to avoid rewrite failures
    have hdiv : ‖(∫ x, ((1 + t * u x)^2 * (2 * Real.log (1 + t * u x)) -
          2 * (t * u x) - 3 * (t * u x)^2) ∂μ) / t^2‖ =
        ‖∫ x, ((1 + t * u x)^2 * (2 * Real.log (1 + t * u x)) -
          2 * (t * u x) - 3 * (t * u x)^2) ∂μ‖ / t^2 := by
      rw [norm_div, show ‖t^2‖ = t^2 from by rw [Real.norm_eq_abs, abs_of_pos ht2pos]]
    rw [hdiv, div_le_iff₀ ht2pos]
    have h_t3 : |t|^3 = |t| * t^2 := by
      calc |t|^3 = |t| * |t|^2 := by ring
        _ = |t| * t^2 := by rw [sq_abs]
    calc ‖∫ x, ((1 + t * u x)^2 * (2 * Real.log (1 + t * u x)) - 2 * (t * u x) - 3 * (t * u x)^2) ∂μ‖
        ≤ ∫ x, ‖(1 + t * u x)^2 * (2 * Real.log (1 + t * u x)) - 2 * (t * u x) - 3 * (t * u x)^2‖ ∂μ :=
            norm_integral_le_integral_norm _
      _ ≤ ∫ x, (14 * M * |t|^3) * u x^2 ∂μ := by
            apply integral_mono_of_nonneg (ae_of_all _ fun _ => norm_nonneg _)
            · exact (hu2.const_mul (14 * M * |t|^3)).congr
                (ae_of_all _ fun x => by ring)
            · exact ae_of_all _ fun x => by
                simp only [Real.norm_eq_abs]; exact R_bound hM t x (htux x)
      _ = (14 * M * c * |t|) * t^2 := by
            rw [integral_const_mul, h_t3]; ring
  have h_R : Tendsto
      (fun t => (∫ x, ((1 + t * u x)^2 * (2 * Real.log (1 + t * u x)) -
        2 * (t * u x) - 3 * (t * u x)^2) ∂μ) / t^2)
      (nhdsWithin 0 {0}ᶜ) (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    exact squeeze_zero'
      (Filter.Eventually.of_forall fun _ => norm_nonneg _)
      h_bound h_lim_t
  have h_goal : Tendsto (fun t => (3*c) +
        (∫ x, ((1 + t * u x)^2 * (2 * Real.log (1 + t * u x)) -
          2 * (t * u x) - 3 * (t * u x)^2) ∂μ) / t^2)
      (nhdsWithin 0 {0}ᶜ) (nhds (3*c)) := by
    have := h_R.const_add (3*c); simp only [add_zero] at this; exact this
  have heq_ev : ∀ᶠ t in nhdsWithin 0 {0}ᶜ,
      (3*c) + (∫ x, ((1 + t * u x)^2 * (2 * Real.log (1 + t * u x)) -
        2 * (t * u x) - 3 * (t * u x)^2) ∂μ) / t^2
      = (∫ x, (1 + t * u x) ^ 2 * Real.log ((1 + t * u x) ^ 2) ∂μ) / t ^ 2 := by
    filter_upwards [hev_small, hev_ne] with t htux ht_ne
    have hpoly_int : Integrable (fun x => 2 * (t * u x) + 3 * (t * u x)^2) μ := by
      apply Integrable.congr ((hu1.const_mul (2 * t)).add (hu2.const_mul (3 * t^2)))
      filter_upwards with x
      show (2 * t) * u x + (3 * t ^ 2) * u x ^ 2 = 2 * (t * u x) + 3 * (t * u x) ^ 2
      ring
    have htux_pos : ∀ x, 0 < 1 + t * u x := fun x => by
      have := htux x; linarith [neg_abs_le (t * u x)]
    have heq_int : (fun x => (1 + t * u x)^2 * Real.log ((1 + t * u x)^2)) =
        fun x => (2 * (t * u x) + 3 * (t * u x)^2) +
          ((1 + t * u x)^2 * (2 * Real.log (1 + t * u x)) - 2 * (t * u x) - 3 * (t * u x)^2) := by
      ext x
      have hlog : Real.log ((1 + t * u x)^2) = 2 * Real.log (1 + t * u x) := by
        rw [show (1 + t * u x)^2 = (1 + t * u x) * (1 + t * u x) by ring]
        rw [Real.log_mul (htux_pos x).ne' (htux_pos x).ne']
        ring
      rw [hlog]; ring
    rw [heq_int, integral_add hpoly_int (hR_int_of t htux), add_div, h_poly t ht_ne]
  exact h_goal.congr' heq_ev

end YangMills
