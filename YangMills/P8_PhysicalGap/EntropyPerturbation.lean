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
  have heq : (fun x => (1 + t * u x) ^ 2) = fun x => (1 + 2 * t * u x) + t ^ 2 * u x ^ 2 := by
    ext x; ring
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

lemma hasDerivAt_sq_mul_2log :
    HasDerivAt (fun s : ℝ => s ^ 2 * (2 * Real.log s)) 2 1 := by
  have hd1 : HasDerivAt (fun s : ℝ => s ^ 2) 2 1 := by
    have := hasDerivAt_pow 2 (1 : ℝ); simp at this; exact this
  have hd2 : HasDerivAt (fun s : ℝ => 2 * Real.log s) 2 1 := by
    have h := (Real.hasDerivAt_log one_ne_zero).const_mul 2; simp at h; exact h
  exact (hd1.mul hd2).congr_deriv (by norm_num [Real.log_one])

lemma hasDerivAt_shift :
    HasDerivAt (fun u : ℝ => (1 + u) ^ 2 * (2 * Real.log (1 + u))) 2 0 := by
  have hinner : HasDerivAt (fun u : ℝ => 1 + u) 1 0 := (hasDerivAt_id 0).const_add 1
  have hbase' : HasDerivAt (fun s : ℝ => s ^ 2 * (2 * Real.log s)) 2 (1 + 0) :=
    hasDerivAt_sq_mul_2log
  have hcomp := HasDerivAt.comp 0 hbase' hinner
  change HasDerivAt (fun u => (1 + u) ^ 2 * (2 * log (1 + u))) (2 * 1) 0 at hcomp
  exact hcomp.congr_deriv (by norm_num)

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
    have hdist : 1 - |y| ≥ 1/2 := by linarith
    apply div_le_div_of_nonneg_left (by positivity) (by norm_num) hdist
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
  calc |(2 + 4*h + 2*h^2) * E - h^4|
      ≤ |(2 + 4*h + 2*h^2) * E| + |-h^4| := abs_add_le _ _
    _ = |2 + 4*h + 2*h^2| * |E| + |h|^4 := by rw [abs_mul, abs_neg, abs_pow]
    _ ≤ 6 * (2 * |h|^3) + (1/2) * |h|^3 := by nlinarith [abs_nonneg E]
    _ = 14 * |h|^3 := by ring_nf; nlinarith [abs_nonneg h]

lemma norm_term_tendsto (c : ℝ) :
    Tendsto (fun t : ℝ => (1 + t ^ 2 * c) * Real.log (1 + t ^ 2 * c) / t ^ 2)
      (nhdsWithin 0 {0}ᶜ) (nhds c) := by
  by_cases hc : c = 0
  · have hfun : (fun t : ℝ => (1 + t ^ 2 * c) * Real.log (1 + t ^ 2 * c) / t ^ 2) = fun _ => 0 := by
      ext t; simp [hc]
    rw [hfun]; simpa [hc] using tendsto_const_nhds
  · let g : ℝ → ℝ := fun s => (1 + s) * Real.log (1 + s)
    have hg : HasDerivAt g 1 0 := by
      have h1 : HasDerivAt (fun s : ℝ => 1 + s) 1 0 := (hasDerivAt_id 0).const_add 1
      have hlog : HasDerivAt (fun s : ℝ => log (1 + s)) 1 0 := by
        have hb' : HasDerivAt Real.log 1 (1 + 0) :=
          Real.hasDerivAt_log (by norm_num : (1:ℝ) ≠ 0)
        have hcomp := HasDerivAt.comp 0 hb' h1
        change HasDerivAt (fun s => log (1 + s)) (1 * 1) 0 at hcomp
        exact hcomp.congr_deriv (by norm_num)
      simpa [g] using h1.mul hlog
    have hmap : Tendsto (fun t => t^2 * c) (nhdsWithin 0 {0}ᶜ) (nhdsWithin 0 {0}ᶜ) := by
      apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      · simpa using (continuous_pow 2).continuousAt.tendsto.const_mul c
      · filter_upwards [self_mem_nhdsWithin] with t ht
        exact Set.mem_compl_singleton_iff.mpr (mul_ne_zero
          (pow_ne_zero 2 (Set.mem_compl_singleton_iff.mp ht)) hc)
    have hlim := (hasDerivAt_iff_tendsto.mp hg).comp hmap
    simp only [g, sub_zero] at hlim
    simpa [mul_one] using (hlim.const_mul c).congr'
      (eventually_nhdsWithin_of_forall fun t ht => by
        field_simp [pow_ne_zero 2 ht]; ring)

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
    apply ((integrable_const 1).add hu2).mono' hu.aestronglyMeasurable
    exact ae_of_all _ fun x => by
      have : 0 ≤ (|u x| - 1) ^ 2 := sq_nonneg _
      simp only [Real.norm_eq_abs]
      nlinarith [sq_abs (u x), abs_nonneg (u x)]
  set c := ∫ x, u x ^ 2 ∂μ
  have hnorm_id : ∀ t : ℝ, ∫ x, (1 + t * u x) ^ 2 ∂μ = 1 + t ^ 2 * c :=
    fun t => integral_one_add_mul_sq μ u t hu1 hu2 hcenter
  simp_rw [hnorm_id]
  have h_abs_t : Tendsto (fun t => |t|) (nhdsWithin 0 {0}ᶜ) (nhds 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds (by simpa using continuous_abs.tendsto 0)
  have hev_small : ∀ᶠ t in nhdsWithin 0 {0}ᶜ, ∀ x, |t * u x| ≤ 1/2 := by
    filter_upwards [(h_abs_t.const_mul M).eventually (Iic_mem_nhds (by norm_num : (0:ℝ) < 1/2))]
      with t ht x
    calc |t * u x| = |t| * |u x| := abs_mul t (u x)
      _ ≤ |t| * M := mul_le_mul_of_nonneg_left (hM x) (abs_nonneg t)
      _ ≤ 1/2 := by nlinarith [abs_nonneg t]
  have hev_ne : ∀ᶠ t in nhdsWithin 0 {0}ᶜ, t ≠ 0 :=
    eventually_nhdsWithin_of_forall Set.mem_compl_singleton_iff.mp
  have h_norm := norm_term_tendsto c
  suffices h_int : Tendsto
      (fun t => (∫ x, (1+t*u x)^2 * log ((1+t*u x)^2) ∂μ) / t^2)
      (nhdsWithin 0 {0}ᶜ) (nhds (3 * c)) by
    have h_diff := h_int.sub h_norm
    simp only [show 3 * c - c = 2 * c by ring] at h_diff
    apply h_diff.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    field_simp [pow_ne_zero 2 ht]
  have h_poly : ∀ t : ℝ, t ≠ 0 →
      (∫ x, (2 * (t * u x) + 3 * (t * u x) ^ 2) ∂μ) / t ^ 2 = 3 * c := by
    intro t ht
    rw [show (fun x => 2 * (t * u x) + 3 * (t * u x) ^ 2) =
        fun x => (2 * t) * u x + (3 * t ^ 2) * u x ^ 2 from by ext x; ring,
        integral_add (hu1.const_mul _) (hu2.const_mul _),
        integral_const_mul, integral_const_mul, hcenter, mul_zero, zero_add]
    field_simp [pow_ne_zero 2 ht]; ring
  have h_split : ∀ᶠ t in nhdsWithin 0 {0}ᶜ,
      (∫ x, (1 + t * u x) ^ 2 * Real.log ((1 + t * u x) ^ 2) ∂μ) / t ^ 2 =
      3 * c + (∫ x, ((1 + t * u x) ^ 2 * (2 * Real.log (1 + t * u x)) -
        2 * (t * u x) - 3 * (t * u x) ^ 2) ∂μ) / t ^ 2 := by
    filter_upwards [hev_small, hev_ne] with t htux ht0
    have hR_int : Integrable (fun x =>
        (1 + t * u x) ^ 2 * (2 * Real.log (1 + t * u x)) -
        2 * (t * u x) - 3 * (t * u x) ^ 2) μ := by
      apply (hu2.const_mul (14 * M * |t| * t ^ 2)).mono'
      · fun_prop
      · exact ae_of_all _ fun x => by
          simp only [Real.norm_eq_abs]
          calc |(1 + t * u x) ^ 2 * (2 * log (1 + t * u x)) - 2*(t*u x) - 3*(t*u x)^2|
              ≤ 14 * |t * u x| ^ 3 := sq_log_expansion_bound (htux x)
            _ ≤ (14 * M * |t| * t ^ 2) * |u x ^ 2| := by
                have : |t * u x| ^ 3 = |t| ^ 3 * |u x| ^ 3 := by rw [abs_mul]; ring
                rw [abs_pow, sq_abs]
                nlinarith [hM x, abs_nonneg t, abs_nonneg (u x),
                           sq_nonneg (u x), sq_nonneg t,
                           pow_nonneg (abs_nonneg t) 3,
                           pow_nonneg (abs_nonneg (u x)) 3]
    have hpoly_int : Integrable
        (fun x => 2 * (t * u x) + 3 * (t * u x) ^ 2) μ :=
      (hu1.const_mul (2 * t)).add (hu2.const_mul (3 * t ^ 2)) |>.congr
        (ae_of_all _ fun x => by ring)
    have hI : ∫ x, (1 + t * u x) ^ 2 * Real.log ((1 + t * u x) ^ 2) ∂μ =
        ∫ x, (2*(t*u x) + 3*(t*u x)^2) ∂μ +
        ∫ x, ((1+t*u x)^2*(2*Real.log(1+t*u x)) - 2*(t*u x) - 3*(t*u x)^2) ∂μ := by
      rw [← integral_add hpoly_int hR_int]
      apply integral_congr_ae
      exact ae_of_all _ fun x => by rw [Real.log_pow]; push_cast; ring
    rw [hI, add_div, h_poly t ht0]
  have h_R : Tendsto
      (fun t => (∫ x, ((1+t*u x)^2*(2*log(1+t*u x)) - 2*t*u x - 3*t^2*u x^2) ∂μ) / t^2)
      (nhdsWithin 0 {0}ᶜ) (nhds 0) := by
    apply squeeze_zero_norm'
    · filter_upwards [hev_small, hev_ne] with t htux ht_ne
      have ht2 : (0:ℝ) < t^2 := sq_pos_of_ne_zero ht_ne
      rw [norm_div, Real.norm_eq_abs, abs_of_pos ht2, div_le_iff₀ ht2]
      calc ‖∫ x, ((1+t*u x)^2*(2*log(1+t*u x)) - 2*t*u x - 3*t^2*u x^2) ∂μ‖
          ≤ ∫ x, ‖(1+t*u x)^2*(2*log(1+t*u x)) - 2*t*u x - 3*t^2*u x^2‖ ∂μ :=
              norm_integral_le_integral_norm _
        _ ≤ ∫ x, (14 * M * |t|) * t^2 * u x^2 ∂μ := by
              apply integral_mono_of_nonneg (ae_of_all _ fun _ => norm_nonneg _)
              · exact (hu2.const_mul _).congr (ae_of_all _ fun x => by ring)
              · exact ae_of_all _ fun x => by
                  simp only [Real.norm_eq_abs]
                  calc |(1+t*u x)^2*(2*log(1+t*u x)) - 2*t*u x - 3*t^2*u x^2|
                      ≤ 14 * |t*u x|^3 := by
                          have : 2*t*u x = 2*(t*u x) := by ring
                          have : 3*t^2*u x^2 = 3*(t*u x)^2 := by ring
                          convert sq_log_expansion_bound (htux x) using 2 <;> ring
                    _ ≤ (14 * M * |t|) * t^2 * u x^2 := by
                          nlinarith [hM x, abs_nonneg t, abs_nonneg (u x),
                                     abs_mul t (u x), sq_abs (u x), sq_abs t,
                                     pow_nonneg (abs_nonneg t) 3,
                                     pow_nonneg (abs_nonneg (u x)) 3]
        _ = 14 * M * c * |t| * t^2 := by
              rw [show (fun x => (14*M*|t|)*t^2*u x^2) = fun x => (14*M*|t|*t^2)*u x^2
                  from by ext; ring, integral_const_mul]
              ring
    · simpa using (h_abs_t.const_mul (14 * M * c)).congr' (eventually_of_forall fun _ => by ring)
  exact (h_R.const_add (3 * c)).congr' (h_split.mono fun t h => h.symm)

end YangMills
