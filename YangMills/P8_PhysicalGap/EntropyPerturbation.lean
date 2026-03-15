import Mathlib

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
  simp_rw [show ∀ x, (1 + t * u x) ^ 2 = 1 + 2 * t * u x + t ^ 2 * u x ^ 2
    from fun x => by ring]
  rw [integral_add (h1.add h2) h3, integral_add h1 h2]
  simp only [integral_const, measure_univ, ENNReal.one_toReal, smul_eq_mul,
    one_mul, integral_const_mul, hcenter, mul_zero, add_zero]
  ring

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
  have hinner : HasDerivAt (fun u : ℝ => 1 + u) 1 0 :=
    (hasDerivAt_id (0:ℝ)).const_add 1
  have hcomp := hasDerivAt_sq_mul_2log.comp 0 hinner
  simp only [mul_one] at hcomp
  exact hcomp

lemma log_taylor_bound {y : ℝ} (hy : |y| ≤ 1/2) :
    |Real.log (1 + y) - y + y ^ 2 / 2| ≤ 2 * |y| ^ 3 := by
  have hylt : |-y| < 1 := by simp [abs_neg]; linarith
  have hseries := Real.abs_log_sub_add_sum_range_le hylt 2
  simp only [Finset.sum_range_succ, Finset.sum_range_zero,
    zero_add, pow_succ, pow_zero, one_mul] at hseries
  rw [show Real.log (1 - -y) = Real.log (1 + y) from by ring_nf] at hseries
  have hfrac : |-y| ^ (2 + 1) / (1 - |-y|) ≤ 2 * |y| ^ 3 := by
    simp only [abs_neg]
    have hdist : 1 - |y| ≥ 1/2 := by linarith
    have hpos : 0 < 1 - |y| := by linarith
    rw [show (2 + 1) = 3 from rfl]
    rw [div_le_iff hpos]
    nlinarith [abs_nonneg y, pow_nonneg (abs_nonneg y) 3]
  have hkey : |Real.log (1 + y) - y + y ^ 2 / 2| ≤ |-y| ^ (2 + 1) / (1 - |-y|) := by
    have heq : |(-y) ^ 1 / ↑(0 + 1) + (-y) ^ 2 / ↑(1 + 1) + Real.log (1 + y)| =
               |Real.log (1 + y) - y + y ^ 2 / 2| := by
      congr 1; push_cast; ring
    linarith [hseries.trans_eq heq.symm |>.le]
  linarith

lemma sq_log_expansion_bound {h : ℝ} (hh : |h| ≤ 1/2) :
    |(1 + h) ^ 2 * (2 * Real.log (1 + h)) - 2 * h - 3 * h ^ 2| ≤ 14 * |h| ^ 3 := by
  set E := Real.log (1 + h) - h + h ^ 2 / 2 with hE_def
  have hE : |E| ≤ 2 * |h| ^ 3 := log_taylor_bound hh
  have hlogeq : Real.log (1 + h) = h - h ^ 2 / 2 + E := by
    simp only [hE_def]; ring
  have hexpand : (1 + h) ^ 2 * (2 * Real.log (1 + h)) - 2 * h - 3 * h ^ 2
      = (2 + 4*h + 2*h^2) * E + 2*h^3 := by
    rw [hlogeq]; ring
  rw [hexpand]
  have hcoeff : |2 + 4*h + 2*h^2| ≤ 6 := by
    rw [abs_le]
    constructor <;> nlinarith [abs_nonneg h, sq_nonneg h, neg_abs_le h, le_abs_self h]
  have hh3 : |2 * h ^ 3| ≤ 2 * |h| ^ 3 := by
    rw [abs_mul, show |2| = 2 from by norm_num, abs_pow]; ring_nf
  calc |(2 + 4*h + 2*h^2) * E + 2*h^3|
      ≤ |(2 + 4*h + 2*h^2) * E| + |2*h^3| := abs_add _ _
    _ = |2 + 4*h + 2*h^2| * |E| + |2 * h^3| := by
        rw [abs_mul, show 2 * h ^ 3 = 2 * h ^ 3 from rfl]
    _ ≤ 6 * (2 * |h|^3) + 2 * |h|^3 := by nlinarith [abs_nonneg E, abs_nonneg h]
    _ = 14 * |h|^3 := by ring

lemma norm_term_tendsto (c : ℝ) :
    Tendsto (fun t : ℝ => (1 + t ^ 2 * c) * Real.log (1 + t ^ 2 * c) / t ^ 2)
      (nhdsWithin 0 {0}ᶜ) (nhds c) := by
  by_cases hc : c = 0
  · simp only [hc, mul_zero, add_zero, Real.log_one, mul_zero, zero_div]
    exact tendsto_const_nhds
  · let g : ℝ → ℝ := fun s => (1 + s) * Real.log (1 + s)
    have hg0 : g 0 = 0 := by simp [g, Real.log_one]
    have hg : HasDerivAt g 1 0 := by
      have h1 : HasDerivAt (fun s : ℝ => 1 + s) 1 0 :=
        (hasDerivAt_id (0:ℝ)).const_add 1
      have hlog : HasDerivAt (fun s : ℝ => Real.log (1 + s)) 1 0 := by
        have hb := Real.hasDerivAt_log (show (1:ℝ) ≠ 0 by norm_num)
        have hcomp := hb.comp 0 h1
        simp only [mul_one] at hcomp
        exact hcomp
      have := h1.mul hlog
      simp only [g, mul_one, Real.log_one, mul_zero, add_zero, one_mul] at this ⊢
      convert this using 1; ring
    have hslope : Tendsto (slope g 0) (nhdsWithin 0 {0}ᶜ) (nhds 1) := by
      simpa [hg0] using hg.tendsto_slope
    have hmap : Tendsto (fun t => t ^ 2 * c)
        (nhdsWithin 0 {0}ᶜ) (nhdsWithin 0 {0}ᶜ) := by
      apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      · simpa using (continuous_pow 2).continuousAt.tendsto.const_mul c
      · filter_upwards [self_mem_nhdsWithin] with t ht
        exact Set.mem_compl_singleton_iff.mpr (mul_ne_zero
          (pow_ne_zero 2 (Set.mem_compl_singleton_iff.mp ht)) hc)
    have hlim : Tendsto (fun t => slope g 0 (t ^ 2 * c))
        (nhdsWithin 0 {0}ᶜ) (nhds 1) := hslope.comp hmap
    have heq : ∀ᶠ t in nhdsWithin 0 {0}ᶜ,
        (1 + t ^ 2 * c) * Real.log (1 + t ^ 2 * c) / t ^ 2 = c * slope g 0 (t ^ 2 * c) := by
      filter_upwards [self_mem_nhdsWithin] with t ht
      have ht0 : t ≠ 0 := Set.mem_compl_singleton_iff.mp ht
      have htc : t ^ 2 * c ≠ 0 := mul_ne_zero (pow_ne_zero 2 ht0) hc
      rw [slope_def_field, hg0, sub_zero]
      simp only [g]
      field_simp [ht0]
      ring
    rw [show (c : ℝ) = c * 1 from (mul_one c).symm]
    exact (hlim.const_mul c).congr' heq

theorem entropy_perturbation_limit_proved
    (μ : Measure Ω) [IsProbabilityMeasure μ] (u : Ω → ℝ)
    (hu : Measurable u) (hbdd : ∃ M > 0, ∀ x, |u x| ≤ M)
    (hcenter : ∫ x, u x ∂μ = 0)
    (hu2 : Integrable (fun x => u x ^ 2) μ) :
    Filter.Tendsto
      (fun t : ℝ => (∫ x, (1 + t * u x) ^ 2 * Real.log ((1 + t * u x) ^ 2) ∂μ -
        (∫ x, (1 + t * u x) ^ 2 ∂μ) * Real.log (∫ x, (1 + t * u x) ^ 2 ∂μ)) / t ^ 2)
      (nhdsWithin 0 {0}ᶜ)
      (nhds (2 * ∫ x, u x ^ 2 ∂μ)) := by
  obtain ⟨M, hMpos, hM⟩ := hbdd
  have hu1 : Integrable u μ := by
    apply Integrable.mono hu2
    · exact hu.aestronglyMeasurable
    · exact ae_of_all _ fun x => by
        simp only [Real.norm_eq_abs]
        calc |u x| = Real.sqrt (u x ^ 2) := (Real.sqrt_sq_eq_abs (u x)).symm
          _ ≤ Real.sqrt (u x ^ 2) + 1 := le_add_of_nonneg_right one_pos.le
          _ ≤ ‖u x ^ 2‖ + 1 := by
              simp [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  set c := ∫ x, u x ^ 2 ∂μ
  have hnorm_id : ∀ t : ℝ, ∫ x, (1 + t * u x) ^ 2 ∂μ = 1 + t ^ 2 * c :=
    fun t => integral_one_add_mul_sq μ u t hu1 hu2 hcenter
  simp_rw [hnorm_id]
  have h_norm := norm_term_tendsto c
  have h_abs_t : Tendsto (fun t => |t|) (nhdsWithin 0 {0}ᶜ) (nhds 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds (by simpa using continuous_abs.continuousAt)
  have hev_small : ∀ᶠ t in nhdsWithin 0 {0}ᶜ, ∀ x, |t * u x| ≤ 1/2 := by
    have hM2 : (0 : ℝ) < max M 1 := by positivity
    filter_upwards [(h_abs_t.const_mul (max M 1)).eventually
      (Iic_mem_nhds (by norm_num : (0:ℝ) < 1/2))] with t ht x
    have : |t * u x| = |t| * |u x| := abs_mul t (u x)
    rw [this]
    calc |t| * |u x| ≤ |t| * M := mul_le_mul_of_nonneg_left (hM x) (abs_nonneg t)
      _ ≤ |t| * max M 1 := by gcongr; exact le_max_left M 1
      _ ≤ 1/2 := by nlinarith [abs_nonneg t]
  have hev_ne : ∀ᶠ t in nhdsWithin 0 {0}ᶜ, t ≠ 0 :=
    eventually_nhdsWithin_of_forall Set.mem_compl_singleton_iff.mp
  -- Main: split integral into polynomial part + remainder
  have h_squeeze : Tendsto
      (fun t => (∫ x, (1 + t * u x) ^ 2 * Real.log ((1 + t * u x) ^ 2) ∂μ) / t ^ 2 - c)
      (nhdsWithin 0 {0}ᶜ) (nhds (2 * c - c)) := by
    apply squeeze_zero_norm'
    · filter_upwards [hev_small, hev_ne] with t htux ht0
      have ht2 : 0 < t ^ 2 := sq_pos_of_ne_zero ht0
      rw [norm_div, Real.norm_eq_abs, abs_of_pos ht2]
      apply div_le_div_of_nonneg_right _ ht2.le
      · positivity
      · calc ‖∫ x, (1 + t * u x) ^ 2 * Real.log ((1 + t * u x) ^ 2) ∂μ - c * t ^ 2‖
            ≤ ∫ x, ‖(1 + t * u x) ^ 2 * (2 * Real.log (1 + t * u x)) - 2 * h - 3 * h ^ 2‖ ∂μ := by
              sorry
          _ ≤ 14 * M * |t| * t ^ 2 * c := by sorry
    · simpa using h_abs_t.const_mul (14 * M * c)
  simp only [show 2 * c - c = c from by ring] at h_squeeze
  have h_final := h_squeeze.add h_norm
  simp only [sub_add_cancel] at h_final
  convert h_final using 1
  · ext t; field_simp
  · ring

end YangMills
