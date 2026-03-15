import Mathlib
import YangMills.P8_PhysicalGap.LSItoSpectralGap

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
  have step1 : ∫ x, (1 + t * u x) ^ 2 ∂μ =
      ∫ x, (1 + 2 * t * u x + t ^ 2 * u x ^ 2) ∂μ :=
    integral_congr_ae (ae_of_all _ fun x => by ring)
  have step2 := integral_add (h1.add h2) h3
  have step3 := integral_add h1 h2
  rw [step1, step2, step3]
  simp only [integral_const, smul_eq_mul]
  rw [integral_const_mul, integral_const_mul, hcenter]
  have hmu : μ.real Set.univ = 1 := by simp [Measure.real, measure_univ]
  linarith

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
  have hinner : HasDerivAt (fun u : ℝ => 1 + u) 1 0 := by
    simpa using (hasDerivAt_id (0:ℝ)).const_add 1
  have hbase : HasDerivAt (fun s : ℝ => s ^ 2 * (2 * Real.log s)) 2 (1 + 0) := by
    simpa using hasDerivAt_sq_mul_2log
  have hcomp := hbase.comp 0 hinner
  simp only [mul_one] at hcomp
  exact hcomp

/-! ## Taylor bound for log -/

lemma log_taylor_bound {y : ℝ} (hy : |y| ≤ 1/2) :
    |Real.log (1 + y) - y + y ^ 2 / 2| ≤ 2 * |y| ^ 3 := by
  have hylt : |-y| < 1 := by simp [abs_neg]; linarith
  have hseries := Real.abs_log_sub_add_sum_range_le hylt 2
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Finset.range_zero] at hseries
  simp only [pow_succ, pow_zero, one_mul, Nat.cast_zero, Nat.cast_one, zero_add] at hseries
  have hlog : Real.log (1 - -y) = Real.log (1 + y) := by ring_nf
  rw [hlog] at hseries
  have hfrac : |-y| ^ 3 / (1 - |-y|) ≤ 2 * |y| ^ 3 := by
    simp [abs_neg]
    have h1 : 1 - |y| ≥ 1/2 := by linarith
    have h2 : |y| ^ 3 / (1 - |y|) ≤ |y| ^ 3 / (1/2) := by
      apply div_le_div_of_nonneg_left (by positivity) (by linarith) h1
    linarith
  calc |Real.log (1 + y) - y + y ^ 2 / 2|
      = |(-y) ^ 1 / (0 + 1) + (-y) ^ 2 / (1 + 1) + Real.log (1 + y)| := by ring_nf
    _ ≤ |-y| ^ 3 / (1 - |-y|) := hseries
    _ ≤ 2 * |y| ^ 3 := hfrac

lemma sq_log_expansion_bound {h : ℝ} (hh : |h| ≤ 1/2) :
    |(1 + h) ^ 2 * (2 * Real.log (1 + h)) - 2 * h - 3 * h ^ 2| ≤ 14 * |h| ^ 3 := by
  set E := Real.log (1 + h) - h + h ^ 2 / 2
  have hE : |E| ≤ 2 * |h| ^ 3 := log_taylor_bound hh
  have hlogeq : Real.log (1 + h) = h - h ^ 2 / 2 + E := by simp [E]; ring
  have hexpand :
      (1 + h) ^ 2 * (2 * Real.log (1 + h)) - 2 * h - 3 * h ^ 2
      = (2 + 4*h + 2*h^2) * E + (2*h^3) := by
    rw [hlogeq]; ring
  rw [hexpand]
  have hh2 : |h| ^ 2 ≤ 1/4 := by nlinarith [abs_nonneg h]
  calc |(2 + 4*h + 2*h^2) * E + 2*h^3|
      ≤ |(2 + 4*h + 2*h^2) * E| + |2*h^3| := abs_add _ _
    _ = |2 + 4*h + 2*h^2| * |E| + 2 * |h|^3 := by
        rw [abs_mul]; congr 1; rw [abs_mul]; simp [abs_of_pos]; ring
    _ ≤ 6 * |E| + 2 * |h| ^ 3 := by
        have hcoeff : |2 + 4*h + 2*h^2| ≤ 6 := by
          nlinarith [abs_nonneg h, sq_abs h, abs_le.mp (show |h| ≤ 1 by linarith)]
        nlinarith [abs_nonneg E]
    _ ≤ 6 * (2 * |h|^3) + 2 * |h|^3 := by linarith [abs_nonneg h]
    _ = 14 * |h|^3 := by ring

/-! ## Normalization term limit -/

lemma norm_term_tendsto (c : ℝ) :
    Tendsto (fun t : ℝ => (1 + t ^ 2 * c) * Real.log (1 + t ^ 2 * c) / t ^ 2)
      (nhdsWithin 0 {0}ᶜ) (nhds c) := by
  by_cases hc : c = 0
  · have hfun : (fun t : ℝ => (1 + t ^ 2 * c) * Real.log (1 + t ^ 2 * c) / t ^ 2) =
        fun _ : ℝ => 0 := by funext t; simp [hc]
    rw [hfun]; simpa [hc] using tendsto_const_nhds
  · let g : ℝ → ℝ := fun s => (1 + s) * Real.log (1 + s)
    have hg0 : g 0 = 0 := by simp [g, Real.log_one]
    have hg : HasDerivAt g 1 0 := by
      have h1 : HasDerivAt (fun s : ℝ => 1 + s) 1 0 :=
        (hasDerivAt_id (0 : ℝ)).const_add 1
      have hlog : HasDerivAt (fun s : ℝ => Real.log (1 + s)) 1 0 := by
        have hbase : HasDerivAt Real.log 1 1 := by
          simpa using Real.hasDerivAt_log (by norm_num : (1 : ℝ) ≠ 0)
        simpa using hbase.comp 0 h1
      simpa [g, Real.log_one] using h1.mul hlog
    have hslope : Tendsto (slope g 0) (nhdsWithin 0 ({0}ᶜ : Set ℝ)) (nhds 1) := by
      simpa [hg0] using hg.tendsto_slope
    have hmap : Tendsto (fun t : ℝ => t ^ 2 * c)
        (nhdsWithin 0 ({0}ᶜ : Set ℝ)) (nhdsWithin 0 ({0}ᶜ : Set ℝ)) := by
      apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      · simpa using ((by fun_prop : ContinuousAt (fun t : ℝ => t ^ 2 * c) 0).tendsto.mono_left
            nhdsWithin_le_nhds)
      · apply eventually_nhdsWithin_of_forall
        intro t ht htc
        simp only [mem_compl_iff, mem_singleton_iff] at ht htc
        apply ht
        have ht2 : t ^ 2 = 0 := (mul_eq_zero.mp htc).resolve_right hc
        nlinarith
    have hcomp : Tendsto (fun t : ℝ => slope g 0 (t ^ 2 * c))
        (nhdsWithin 0 ({0}ᶜ : Set ℝ)) (nhds 1) := hslope.comp hmap
    have hmul : Tendsto (fun t : ℝ => c * slope g 0 (t ^ 2 * c))
        (nhdsWithin 0 ({0}ᶜ : Set ℝ)) (nhds (c * 1)) := hcomp.const_mul c
    have heq : (fun t : ℝ => (1 + t ^ 2 * c) * Real.log (1 + t ^ 2 * c) / t ^ 2)
        =ᶠ[nhdsWithin 0 ({0}ᶜ : Set ℝ)] (fun t : ℝ => c * slope g 0 (t ^ 2 * c)) := by
      filter_upwards with t ht
      have ht0 : t ≠ 0 := by simpa [mem_compl_iff, mem_singleton_iff] using ht
      have htc : t ^ 2 * c ≠ 0 := mul_ne_zero (pow_ne_zero 2 ht0) hc
      rw [slope_def_field, hg0]
      simp only [g, sub_zero]
      field_simp
      ring
    simpa [mul_one] using (hmul.congr' heq.symm)

/-! ## Main theorem -/

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
  have hu1 : Integrable u μ :=
    (hu2.mono_fun hu.aestronglyMeasurable
      (ae_of_all _ fun x => by simpa using sq_abs_le_abs (u x))).integrable
  set c := ∫ x, u x ^ 2 ∂μ
  have hnorm_id : ∀ t : ℝ, ∫ x, (1 + t * u x) ^ 2 ∂μ = 1 + t ^ 2 * c :=
    fun t => integral_one_add_mul_sq μ u t hu1 hu2 hcenter
  simp_rw [hnorm_id]

  -- Split (A - B)/t² = A/t² - B/t²
  have hgoal_eq : ∀ᶠ t in nhdsWithin 0 ({0}ᶜ : Set ℝ),
      (∫ x, (1 + t * u x) ^ 2 * Real.log ((1 + t * u x) ^ 2) ∂μ -
        (1 + t ^ 2 * c) * Real.log (1 + t ^ 2 * c)) / t ^ 2 =
      (∫ x, (1 + t * u x) ^ 2 * Real.log ((1 + t * u x) ^ 2) ∂μ) / t ^ 2 -
        (1 + t ^ 2 * c) * Real.log (1 + t ^ 2 * c) / t ^ 2 := by
    apply eventually_nhdsWithin_of_forall; intro t _; rw [sub_div]
  -- The norm term → c
  have h_norm : Tendsto
      (fun t : ℝ => (1 + t ^ 2 * c) * Real.log (1 + t ^ 2 * c) / t ^ 2)
      (nhdsWithin 0 {0}ᶜ) (nhds c) := norm_term_tendsto c
  -- Suffices: ∫(1+tu)²*log((1+tu)²)/t² → 3c
  suffices h_int : Tendsto
      (fun t : ℝ => (∫ x, (1 + t * u x) ^ 2 * Real.log ((1 + t * u x) ^ 2) ∂μ) / t ^ 2)
      (nhdsWithin 0 {0}ᶜ) (nhds (3 * c)) by
    have h_combined := h_int.sub h_norm
    simp only [show 3 * c - c = 2 * c by ring] at h_combined
    exact h_combined.congr' hgoal_eq.symm
  -- Now prove ∫(1+tu)²*log((1+tu)²)/t² → 3c
  -- Write log((1+tu)²) = 2*log(1+tu) for small t (1+tu > 0)
  -- Then (1+tu)²*2*log(1+tu) = 2tu + 3t²u² + R(t,x)
  -- Integrate: 0 + 3t²c + ∫R, divide by t²: 3c + (∫R)/t² → 3c
  -- Main decomposition:
  -- ∫(1+tu)²*log((1+tu)²)/t² = ∫(2tu+3t²u²)/t² + ∫R/t²
  --                           = 3c + (∫R)/t²
  -- where |R(t,x)| ≤ 14*|tu|³ ≤ 14*M*|t|*u²
  have h_poly : ∀ t ≠ (0:ℝ),
      ∫ x, (2 * (t * u x) + 3 * (t * u x) ^ 2) ∂μ / t ^ 2 = 3 * c := by
    intro t ht
    have : ∫ x, (2 * (t * u x) + 3 * (t * u x) ^ 2) ∂μ =
        2 * t * ∫ x, u x ∂μ + 3 * t ^ 2 * c := by
      rw [integral_add (hu1.const_mul _) (hu2.const_mul _)]
      simp [integral_const_mul, mul_comm, mul_assoc]
    rw [this, hcenter]
    field_simp; ring
  -- DCT remainder → 0
  -- |t| → 0 along nhdsWithin 0 {0}ᶜ
  have h_abs_t : Tendsto (fun t : ℝ => |t|)
      (nhdsWithin 0 ({0}ᶜ : Set ℝ)) (nhds 0) := by
    simpa using tendsto_nhdsWithin_of_tendsto_nhds
      (continuous_abs.continuousAt (x := (0:ℝ)).tendsto)
  have h_R : Tendsto
      (fun t : ℝ =>
        ∫ x, ((1 + t * u x) ^ 2 * (2 * Real.log (1 + t * u x))
              - 2 * (t * u x) - 3 * (t * u x) ^ 2) ∂μ / t ^ 2)
      (nhdsWithin 0 {0}ᶜ) (nhds 0) := by
    apply squeeze_zero
    · intro t; positivity
    · -- bound: |∫R/t²| ≤ 14*M²*c*|t|
      intro t
      by_cases ht : t = 0
      · simp [ht]
      · have ht2 : t ^ 2 > 0 := sq_pos_of_ne_zero t ht
        rw [norm_div, Real.norm_eq_abs, abs_of_pos ht2]
        apply div_le_div_of_nonneg_right _ ht2.le
        -- |∫R| ≤ ∫|R| ≤ ∫(14*M²*|t|*u²) = 14*M²*|t|*c
        calc ‖∫ x, ((1 + t * u x) ^ 2 * (2 * Real.log (1 + t * u x))
                - 2 * (t * u x) - 3 * (t * u x) ^ 2) ∂μ‖
            ≤ ∫ x, ‖(1 + t * u x) ^ 2 * (2 * Real.log (1 + t * u x))
                - 2 * (t * u x) - 3 * (t * u x) ^ 2‖ ∂μ :=
              norm_integral_le_integral_norm _
          _ ≤ ∫ x, 14 * M ^ 2 * |t| * u x ^ 2 ∂μ := by
              apply integral_mono
              · exact (hu2.const_mul _).const_mul _  |>.const_mul _  |>.norm
              · exact hu2.const_mul _
              · intro x
                simp only [Real.norm_eq_abs]
                have hux : |t * u x| ≤ 1/2 ∨ ¬(|t * u x| ≤ 1/2) := le_or_lt _ _ |>.imp_right le_of_lt |>.symm.imp id id
                by_cases htux : |t * u x| ≤ 1/2
                · have hbound := sq_log_expansion_bound htux
                  calc |(1 + t * u x) ^ 2 * (2 * Real.log (1 + t * u x))
                          - 2 * (t * u x) - 3 * (t * u x) ^ 2|
                      ≤ 14 * |t * u x| ^ 3 := hbound
                    _ = 14 * |t| ^ 3 * |u x| ^ 3 := by rw [abs_mul]; ring
                    _ ≤ 14 * M ^ 2 * |t| * u x ^ 2 := by
                        have := hM x
                        have hux2 : |u x| ≤ M := this
                        nlinarith [abs_nonneg t, abs_nonneg (u x),
                                   sq_nonneg (u x), sq_abs (u x)]
                · -- |tu| > 1/2: we need |t| small enough, use eventually
                  -- For the squeeze bound, just use a crude estimate
                  -- When |tu| > 1/2, we have |u| > 1/(2M) (if |t| ≤ 1)
                  -- crude: all terms ≤ C*u² for fixed t via boundedness of u
                  have hux_lb : 1/2 < |t * u x| := by
                    push_neg at htux; exact htux
                  -- |t|*|u| > 1/2, so u² ≥ 1/(4t²)
                  have hux2_lb : u x ^ 2 ≥ 1 / (4 * t ^ 2) := by
                    have := sq_abs (t * u x)
                    rw [abs_mul] at hux_lb
                    nlinarith [abs_nonneg t, sq_nonneg t, sq_abs t,
                                sq_abs (u x), abs_nonneg (u x)]
                  -- bound |(1+h)²*2*log(1+h) - 2h - 3h²| ≤ C for |h|≤M (crude)
                  -- use: |log(1+h)| ≤ |log(1-M)| + |log(1+M)| for |h|≤M
                  -- everything ≤ C*M²*u² via hux2_lb
                  nlinarith [sq_nonneg (u x), sq_nonneg (t * u x),
                              abs_nonneg (t * u x), abs_nonneg (u x),
                              hM x, sq_abs (u x), abs_nonneg t,
                              Real.abs_log_le_abs_log (by nlinarith [abs_nonneg (t * u x)] : 0 < 1 + t * u x) (by nlinarith [hM x, abs_nonneg t] : 1 + t * u x ≤ 1 + M)]
          _ = 14 * M ^ 2 * |t| * c := by
              rw [integral_const_mul, integral_const_mul, integral_const_mul]
              simp [c]
    · -- 14*M²*c*|t| → 0
      have hc_bound : Tendsto (fun t : ℝ => 14 * M ^ 2 * c * |t|)
          (nhdsWithin 0 ({0}ᶜ : Set ℝ)) (nhds 0) := by
        simpa using h_abs_t.const_mul (14 * M ^ 2 * c)
      exact hc_bound
  -- Final assembly: (∫(1+tu)²*log((1+tu)²))/t² → 3c
  -- Rewrite log((1+tu)²) = 2*log(1+tu) for small t
  have h_log_sq : ∀ᶠ t in nhdsWithin 0 ({0}ᶜ : Set ℝ),
      ∀ᵐ x ∂μ, (1 + t * u x) ^ 2 * Real.log ((1 + t * u x) ^ 2) =
        (1 + t * u x) ^ 2 * (2 * Real.log (1 + t * u x)) := by
    apply eventually_nhdsWithin_of_forall; intro t _
    apply ae_of_all; intro x
    rw [Real.log_pow]; ring
  -- Split integrand into poly + remainder
  have h_split : ∀ᶠ t in nhdsWithin 0 ({0}ᶜ : Set ℝ),
      (∫ x, (1 + t * u x) ^ 2 * Real.log ((1 + t * u x) ^ 2) ∂μ) / t ^ 2 =
      3 * c + (∫ x, ((1 + t * u x) ^ 2 * (2 * Real.log (1 + t * u x))
                     - 2 * (t * u x) - 3 * (t * u x) ^ 2) ∂μ) / t ^ 2 := by
    filter_upwards [h_log_sq] with t hlog ht
    have ht0 : t ≠ 0 := by simpa [mem_compl_iff] using ht
    have hI : ∫ x, (1 + t * u x) ^ 2 * Real.log ((1 + t * u x) ^ 2) ∂μ =
        ∫ x, (2 * (t * u x) + 3 * (t * u x) ^ 2) ∂μ +
        ∫ x, ((1 + t * u x) ^ 2 * (2 * Real.log (1 + t * u x))
              - 2 * (t * u x) - 3 * (t * u x) ^ 2) ∂μ := by
      rw [← integral_add]
      · apply integral_congr_ae
        filter_upwards [hlog] with x hx
        rw [hx]; ring
      · exact (hu1.const_mul _).add (hu2.const_mul _)
      · -- integrability of remainder: bounded by 14*M²*|t|*u²
        apply Integrable.sub
        · apply Integrable.sub
          · -- (1+tu)²*2*log(1+tu) integrable: bounded * integrable
            exact (hu2.const_mul _).mono_fun
              (hu.aestronglyMeasurable.const_mul _) (ae_of_all _ fun x => by
                simp [Real.norm_eq_abs]; nlinarith [hM x, abs_nonneg (t * u x)])
          · exact (hu1.const_mul _)
        · exact hu2.const_mul _
    rw [hI, add_div, h_poly t ht0]
  suffices h : Tendsto
      (fun t : ℝ => 3 * c +
        (∫ x, ((1 + t * u x) ^ 2 * (2 * Real.log (1 + t * u x))
               - 2 * (t * u x) - 3 * (t * u x) ^ 2) ∂μ) / t ^ 2)
      (nhdsWithin 0 {0}ᶜ) (nhds (3 * c)) by
    exact h.congr' h_split.symm
  simpa using h_R.const_add (3 * c)

end YangMills
