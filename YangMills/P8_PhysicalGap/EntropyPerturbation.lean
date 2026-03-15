import Mathlib
import YangMills.P8_PhysicalGap.LSItoSpectralGap

/-!
# Entropy Perturbation Limit

Proves `entropy_perturbation_limit` from `LSItoSpectralGap.lean`.

## Mathematical content

The full entropy functional is:
  Ent_μ(f) = ∫ f*log(f) dμ - (∫ f dμ)*log(∫ f dμ)

For f_t = (1+tu)², with ∫u=0 and ∫u²<∞:
  Ent_μ(f_t)/t² → 2*∫u² dμ  as t→0

**Key cancellation**: The divergent parts of ∫f*log(f)/t² and (∫f)*log(∫f)/t²
cancel each other. Neither term alone has a finite limit.

Specifically:
  ∫(1+tu)²*log((1+tu)²) ≈ 2t²∫u² * log(?) + ...  [diverges alone]
  (∫(1+tu)²)*log(∫(1+tu)²) ≈ (1+t²∫u²)*log(1+t²∫u²) → cancels divergence

## Proved here

- `integral_one_add_mul_sq`: ∫(1+tu)² = 1 + t²∫u²  (Lemma A) ✅
- `pos_of_small_t`: 1+tu > 0 for |t| < 1/(2M)  (Lemma B) ✅
- `hasDerivAt_sq_mul_2log`: HasDerivAt (s²*(2*log s)) 2 1  ✅
- `hasDerivAt_shift`: HasDerivAt ((1+u)²*(2*log(1+u))) 2 0  ✅

## Sorrys remaining

- `entropy_perturbation_seq`: the full DCT argument combining the two terms
  Strategy: seq characterization + dominated convergence + pointwise cancellation
  The divergent parts cancel: ∫(1+tu)²*log((1+tu)²)/t² - (1+t²c)*log(1+t²c)/t²
  where c = ∫u². Each term diverges but the difference → 2c.
-/

namespace YangMills

open MeasureTheory Real Filter Set

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ## Lemma A: ∫(1+tu)² = 1 + t²∫u² -/

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

/-! ## Lemma B: positivity -/

lemma pos_of_small_t {u : Ω → ℝ} {M : ℝ} (hMpos : 0 < M)
    (hM : ∀ x, |u x| ≤ M) {t : ℝ} (ht : |t| < 1 / (2 * M)) (x : Ω) :
    0 < 1 + t * u x := by
  have h1 : |t * u x| < 1 / 2 := by
    calc |t * u x| = |t| * |u x| := abs_mul t (u x)
    _ ≤ |t| * M := mul_le_mul_of_nonneg_left (hM x) (abs_nonneg t)
    _ < 1 / (2 * M) * M := mul_lt_mul_of_pos_right ht hMpos
    _ = 1 / 2 := by field_simp
  linarith [neg_abs_le (t * u x)]

/-! ## Calculus lemmas for the kernel -/

/-- Composition: map t ↦ 1+t·a takes nhdsWithin 0 {0}ᶜ to nhdsWithin 1 {1}ᶜ. -/
lemma tendsto_nhdsWithin_one_add_mul (a : ℝ) (ha : a ≠ 0) :
    Tendsto (fun t : ℝ => 1 + t * a)
      (nhdsWithin 0 {0}ᶜ) (nhdsWithin 1 {1}ᶜ) := by
  apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
  · simpa using (by fun_prop : ContinuousAt (fun t : ℝ => 1 + t * a) 0).tendsto.mono_left
      nhdsWithin_le_nhds
  · apply eventually_nhdsWithin_of_forall
    intro t ht h
    simp only [mem_compl_iff, mem_singleton_iff] at ht
    simp only [mem_singleton_iff] at h
    exact ht ((mul_eq_zero.mp (by linarith)).resolve_right ha)

/-- HasDerivAt of s²·(2·log s) at s=1 equals 2. -/
lemma hasDerivAt_sq_mul_2log :
    HasDerivAt (fun s : ℝ => s ^ 2 * (2 * Real.log s)) 2 1 := by
  have hd1 : HasDerivAt (fun s : ℝ => s ^ 2) 2 1 := by
    have := hasDerivAt_pow 2 (1 : ℝ); simp at this; exact this
  have hd2 : HasDerivAt (fun s : ℝ => 2 * Real.log s) 2 1 := by
    have h := (Real.hasDerivAt_log one_ne_zero).const_mul 2; simp at h; exact h
  exact (hd1.mul hd2).congr_deriv (by norm_num [Real.log_one])

/-- HasDerivAt of (1+u)²·(2·log(1+u)) at u=0 equals 2. -/
lemma hasDerivAt_shift :
    HasDerivAt (fun u : ℝ => (1 + u) ^ 2 * (2 * Real.log (1 + u))) 2 0 := by
  have hinner : HasDerivAt (fun u : ℝ => 1 + u) 1 0 := by
    simpa using (hasDerivAt_id (0:ℝ)).const_add 1
  have hbase : HasDerivAt (fun s : ℝ => s ^ 2 * (2 * Real.log s)) 2 (1 + 0) := by
    simpa using hasDerivAt_sq_mul_2log
  have hcomp := hbase.comp 0 hinner
  simp only [mul_one] at hcomp
  exact hcomp

/-! ## Main theorem -/

/-- Sequential version of entropy perturbation limit.
    Status: sorry — requires pointwise cancellation of divergent terms + DCT.
    Strategy: for each sequence tₙ→0, show the integrand converges pointwise
    and is dominated by an integrable bound. -/
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
  -- Use sequential characterization since nhdsWithin 0 {0}ᶜ is countably generated
  rw [tendsto_iff_seq_tendsto]
  intro s hs
  -- For each sequence sₙ → 0, sₙ ≠ 0, the ratio → 2∫u²
  -- Proof uses: integral_one_add_mul_sq (for normalization term)
  --             pos_of_small_t (for log to be defined)
  --             hasDerivAt_shift (for pointwise expansion)
  --             tendsto_integral_filter_of_dominated_convergence (DCT)
  sorry

end YangMills
