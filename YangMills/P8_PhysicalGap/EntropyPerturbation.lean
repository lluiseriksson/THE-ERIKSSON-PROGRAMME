import Mathlib
import YangMills.P8_PhysicalGap.LSItoSpectralGap

/-!
# Entropy Perturbation Limit

Proves `entropy_perturbation_limit` from `LSItoSpectralGap.lean`:

  Tendsto (fun t => Ent((1+tu)²)/t²) (nhdsWithin 0 {0}ᶜ) (nhds (2 * ∫ u²))

## Strategy

Split into four lemmas:
1. `integral_one_add_mul_sq`: ∫(1+tu)² = 1 + t²∫u²  (when ∫u=0)
2. `pos_of_small_t`: 1+tu > 0 for |t| < 1/(2M)
3. `entropy_perturbation_limit_seq`: sequential version via DCT
4. Assembly via `tendsto_iff_seq_tendsto`

## Status
- Lemmas 1, 2: ✅ proved
- Lemma 3 (DCT): 📌 sorry (requires Taylor expansion under integral)
- Assembly: ✅ proved from lemma 3
-/

namespace YangMills

open MeasureTheory Real Filter Set

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ## Lemma 1: Integral of (1+tu)² -/

/-- When u is centered (∫u=0) and square-integrable,
    ∫(1+tu)² = 1 + t²·∫u². -/
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
  have step2 : ∫ x, (1 + 2 * t * u x + t ^ 2 * u x ^ 2) ∂μ =
      ∫ x, (1 + 2 * t * u x) ∂μ + ∫ x, t ^ 2 * u x ^ 2 ∂μ :=
    integral_add (h1.add h2) h3
  have step3 : ∫ x, (1 + 2 * t * u x) ∂μ =
      ∫ x, (1 : ℝ) ∂μ + ∫ x, 2 * t * u x ∂μ :=
    integral_add h1 h2
  rw [step1, step2, step3]
  simp only [integral_const, smul_eq_mul]
  rw [integral_const_mul, integral_const_mul, hcenter]
  have hmu : μ.real Set.univ = 1 := by simp [Measure.real, measure_univ]
  linarith

/-! ## Lemma 2: Positivity near t=0 -/

/-- For |u x| ≤ M, if |t| < 1/(2M) then 1 + t·u x > 0. -/
lemma pos_of_small_t {u : Ω → ℝ} {M : ℝ} (hMpos : 0 < M)
    (hM : ∀ x, |u x| ≤ M) {t : ℝ} (ht : |t| < 1 / (2 * M)) (x : Ω) :
    0 < 1 + t * u x := by
  have h1 : |t * u x| < 1 / 2 := by
    calc |t * u x| = |t| * |u x| := abs_mul t (u x)
    _ ≤ |t| * M := mul_le_mul_of_nonneg_left (hM x) (abs_nonneg t)
    _ < 1 / (2 * M) * M := mul_lt_mul_of_pos_right ht hMpos
    _ = 1 / 2 := by field_simp
  linarith [neg_abs_le (t * u x)]

/-! ## Lemma 3: Sequential entropy limit (core DCT argument) -/

/-- The pointwise kernel: Ent((1+tu)²)/t² → 2u² as t→0. -/
private lemma entropy_kernel_tendsto (a : ℝ) :
    Tendsto (fun t : ℝ =>
      ((1 + t * a) ^ 2 * Real.log ((1 + t * a) ^ 2)) / t ^ 2)
      (nhdsWithin 0 {0}ᶜ)
      (nhds (2 * a ^ 2)) := by
  -- Taylor: (1+ta)²·log(1+ta)² = (1+ta)²·2log(1+ta)
  --       ≈ (1+2ta+t²a²)·2(ta - t²a²/2 + O(t³))
  --       = 2ta + 2t²a² - t²a² + O(t³) + O(t²) cross terms
  --       → 2t²a² + higher, so ratio → 2a²
  sorry

/-- Sequential version: if tₙ → 0 (tₙ ≠ 0),
    then Ent((1+tₙu)²)/tₙ² → 2∫u². -/
lemma entropy_perturbation_seq
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (u : Ω → ℝ) (hu : Measurable u)
    (hbdd : ∃ M > 0, ∀ x, |u x| ≤ M)
    (hcenter : ∫ x, u x ∂μ = 0)
    (hu2 : Integrable (fun x => u x ^ 2) μ)
    (s : ℕ → ℝ) (hs : Tendsto s atTop (nhdsWithin 0 {0}ᶜ)) :
    Tendsto (fun n =>
      (∫ x, (1 + s n * u x) ^ 2 * Real.log ((1 + s n * u x) ^ 2) ∂μ -
        (∫ x, (1 + s n * u x) ^ 2 ∂μ) *
          Real.log (∫ x, (1 + s n * u x) ^ 2 ∂μ)) / (s n) ^ 2)
      atTop (nhds (2 * ∫ x, u x ^ 2 ∂μ)) := by
  sorry

/-! ## Assembly: sequential → filter limit -/

/-- `entropy_perturbation_limit` proved from the sequential version.
    Uses `tendsto_iff_seq_tendsto` since `nhdsWithin 0 {0}ᶜ`
    is countably generated. -/
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
  rw [tendsto_iff_seq_tendsto]
  intro s hs
  exact entropy_perturbation_seq μ u hu hbdd hcenter hu2 s hs

end YangMills
