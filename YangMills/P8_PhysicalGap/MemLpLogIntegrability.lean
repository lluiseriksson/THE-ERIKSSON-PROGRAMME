import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# MemLpLogIntegrability — Σ-path helper lemma

The single helper that closes the Σ path: under `MemLp f p μ` with `2 < p`
on a finite measure space, `fun x ↦ (f x)² · log((f x)²)` is integrable.

Used by `BalabanToLSI.lean`'s Σ chain (specifically in
`lsi_normalized_gibbs_from_haar_memLp`) to discharge the integrability
obligation that forces the vanilla universal-measurable-f LSI statement to
carry an ad-hoc `sorry` at line 805 of that file.

## Mathematical content

Pointwise for real `u` and `δ > 0`:
* if `u² ≤ 1`, `|u² · log(u²)| ≤ 1` (from `abs_log_mul_self_lt`, plus the
  convention `Real.log 0 = 0`);
* if `u² > 1`, `log(u²) > 0` and `log(u²) ≤ (u²)^δ / δ`, hence
  `u² · log(u²) ≤ u² · (u²)^δ / δ`.

With `δ := (q.toReal - 2)/2` for some finite `q ∈ (2, p]`, a routine
`rpow_add` computation gives `u² · (u²)^δ = |u|^q.toReal`, so
`|u² · log(u²)| ≤ 1 + |u|^q.toReal / δ` pointwise. The RHS is integrable
because the constant is integrable on a finite measure and
`|f|^q.toReal ∈ L¹(μ)` is exactly `MemLp.integrable_norm_rpow'`. The
`p = ⊤` case reduces to `q := 3` via `MemLp.mono_exponent`.

Nothing here depends on any YangMills definitions; only Mathlib.
-/

namespace YangMills

open MeasureTheory
open scoped ENNReal Real

/-- Pointwise bound: for any real `u` and `δ > 0`,
    `|u² · log(u²)| ≤ 1 + u² · (u²)^δ / δ`. -/
private lemma abs_sq_mul_log_sq_le {u δ : ℝ} (hδ : 0 < δ) :
    |u ^ 2 * Real.log (u ^ 2)| ≤ 1 + u ^ 2 * (u ^ 2) ^ δ / δ := by
  set v : ℝ := u ^ 2 with hv_def
  have hv_nn : 0 ≤ v := sq_nonneg u
  have hvpow_nn : 0 ≤ v ^ δ := Real.rpow_nonneg hv_nn δ
  have hrhs_extra_nn : 0 ≤ v * v ^ δ / δ :=
    div_nonneg (mul_nonneg hv_nn hvpow_nn) hδ.le
  rcases le_or_gt v 1 with hle | hlt
  · -- v ≤ 1 case: |v · log v| ≤ 1 ≤ 1 + v * v^δ / δ
    have h_bound : |v * Real.log v| ≤ 1 := by
      rcases eq_or_lt_of_le hv_nn with hv_eq | hv_pos
      · rw [← hv_eq]; simp
      · have hv_ne : v ≠ 0 := ne_of_gt hv_pos
        have hlog_le : Real.log v ≤ 0 := Real.log_nonpos hv_nn hle
        have h_vlog_le : v * Real.log v ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos hv_nn hlog_le
        rw [abs_of_nonpos h_vlog_le]
        have h_vinv_pos : 0 < v⁻¹ := inv_pos.mpr hv_pos
        have h_log_sub : Real.log v⁻¹ ≤ v⁻¹ - 1 :=
          Real.log_le_sub_one_of_pos h_vinv_pos
        have h_neg_eq : -(v * Real.log v) = v * Real.log v⁻¹ := by
          rw [Real.log_inv]; ring
        rw [h_neg_eq]
        have h_step : v * Real.log v⁻¹ ≤ v * (v⁻¹ - 1) :=
          mul_le_mul_of_nonneg_left h_log_sub hv_nn
        have h_calc : v * (v⁻¹ - 1) = 1 - v := by
          rw [mul_sub, mul_inv_cancel₀ hv_ne, mul_one]
        linarith
    linarith [hrhs_extra_nn]
  · -- 1 < v case: log v > 0 and log v ≤ v^δ / δ.
    have hv_pos : 0 < v := lt_trans zero_lt_one hlt
    have hlog_pos : 0 < Real.log v := Real.log_pos hlt
    have hlog_le : Real.log v ≤ v ^ δ / δ := Real.log_le_rpow_div hv_nn hδ
    have h_mul_le : v * Real.log v ≤ v * (v ^ δ / δ) :=
      mul_le_mul_of_nonneg_left hlog_le hv_nn
    have h_rearr : v * (v ^ δ / δ) = v * v ^ δ / δ := by ring
    have h_vlog_nn : 0 ≤ v * Real.log v := mul_nonneg hv_nn hlog_pos.le
    rw [abs_of_nonneg h_vlog_nn]
    linarith

/-- Key identity: for real `u` and `r ≥ 2`,
    `u² · (u²)^((r-2)/2) = |u|^r`. -/
private lemma sq_mul_rpow_eq_abs_rpow {u r : ℝ} (hr : 2 ≤ r) :
    u ^ 2 * (u ^ 2) ^ ((r - 2) / 2) = |u| ^ r := by
  set δ : ℝ := (r - 2) / 2 with hδ_def
  have habs_nn : (0 : ℝ) ≤ |u| := abs_nonneg u
  have hδ_nn : (0 : ℝ) ≤ δ := by
    show 0 ≤ (r - 2) / 2
    have : 0 ≤ r - 2 := by linarith
    positivity
  have h2δ_nn : (0 : ℝ) ≤ 2 * δ := by positivity
  have hu2_abs : u ^ 2 = |u| ^ 2 := (sq_abs u).symm
  have hu2_rpow : u ^ 2 = |u| ^ (2 : ℝ) := by
    rw [hu2_abs, Real.rpow_two]
  calc u ^ 2 * (u ^ 2) ^ δ
      = |u| ^ (2 : ℝ) * (|u| ^ (2 : ℝ)) ^ δ := by rw [hu2_rpow]
    _ = |u| ^ (2 : ℝ) * |u| ^ ((2 : ℝ) * δ) := by
          rw [← Real.rpow_mul habs_nn]
    _ = |u| ^ ((2 : ℝ) + 2 * δ) := by
          rw [← Real.rpow_add_of_nonneg habs_nn (by norm_num : (0 : ℝ) ≤ 2) h2δ_nn]
    _ = |u| ^ r := by
          congr 1
          show (2 : ℝ) + 2 * δ = r
          rw [hδ_def]; ring

/-- **Σ-closure helper.** On a finite measure space, `MemLp f p μ` with
`2 < p` implies `fun x ↦ (f x)² · log((f x)²)` is integrable.

This is the exact premise whose absence forces the `sorry` at
`BalabanToLSI.lean:805` under the vanilla universal-measurable-f LSI; the
MemLp-gated Σ chain calls this lemma at that call-site and closes the gap. -/
theorem memLp_gt_two_integrable_sq_mul_log_sq
    {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    [MeasureTheory.IsFiniteMeasure μ] (f : Ω → ℝ) (p : ℝ≥0∞) (hp : 2 < p)
    (hf : MeasureTheory.MemLp f p μ) :
    MeasureTheory.Integrable (fun x => f x ^ 2 * Real.log (f x ^ 2)) μ := by
  -- Step 1: reduce to a finite exponent q > 2 via `MemLp.mono_exponent`.
  set q : ℝ≥0∞ := min p 3 with hq_def
  have h3_ne_top : (3 : ℝ≥0∞) ≠ ⊤ := ENNReal.ofNat_ne_top
  have hq_le_p : q ≤ p := min_le_left _ _
  have hq_le_three : q ≤ 3 := min_le_right _ _
  have h2_lt_three : (2 : ℝ≥0∞) < 3 := by norm_num
  have hq_gt_two : (2 : ℝ≥0∞) < q := lt_min hp h2_lt_three
  have hq_ne_top : q ≠ ⊤ := ne_top_of_le_ne_top h3_ne_top hq_le_three
  have hf_q : MeasureTheory.MemLp f q μ := hf.mono_exponent hq_le_p
  -- Step 2: set r = q.toReal; show 2 < r.
  set r : ℝ := q.toReal with hr_def
  have h2_ne_top : (2 : ℝ≥0∞) ≠ ⊤ := ENNReal.ofNat_ne_top
  have hr_gt_two : (2 : ℝ) < r := by
    have h := (ENNReal.toReal_lt_toReal h2_ne_top hq_ne_top).mpr hq_gt_two
    simpa [hr_def] using h
  have hr_ge_two : 2 ≤ r := le_of_lt hr_gt_two
  -- Step 3: δ := (r - 2)/2 > 0 is the Young-type slack exponent.
  set δ : ℝ := (r - 2) / 2 with hδ_def
  have hδ_pos : 0 < δ := by
    show 0 < (r - 2) / 2
    have h2 : 0 < r - 2 := by linarith
    positivity
  -- Step 4: AEStronglyMeasurable of the integrand.
  have hf_meas : AEStronglyMeasurable f μ := hf_q.aestronglyMeasurable
  have hf_sq_meas : AEStronglyMeasurable (fun x => f x ^ 2) μ := hf_meas.pow 2
  have hint_meas :
      AEStronglyMeasurable (fun x => f x ^ 2 * Real.log (f x ^ 2)) μ := by
    have hlog_meas : Measurable Real.log := Real.measurable_log
    have hlog_sq : AEStronglyMeasurable (fun x => Real.log (f x ^ 2)) μ :=
      (hlog_meas.comp_aemeasurable hf_sq_meas.aemeasurable).aestronglyMeasurable
    exact hf_sq_meas.mul hlog_sq
  -- Step 5: integrability of the dominating function `1 + ‖f·‖^r / δ`.
  have hint_pow : MeasureTheory.Integrable (fun x => ‖f x‖ ^ r) μ := by
    have h := hf_q.integrable_norm_rpow'
    simpa [hr_def] using h
  have hint_const : MeasureTheory.Integrable (fun _ : Ω => (1 : ℝ)) μ :=
    MeasureTheory.integrable_const 1
  have hint_pow_div : MeasureTheory.Integrable (fun x => ‖f x‖ ^ r / δ) μ :=
    hint_pow.div_const δ
  have hint_bound :
      MeasureTheory.Integrable (fun x => 1 + ‖f x‖ ^ r / δ) μ :=
    hint_const.add hint_pow_div
  -- Step 6: pointwise bound.
  have h_point : ∀ x, |f x ^ 2 * Real.log (f x ^ 2)|
      ≤ 1 + ‖f x‖ ^ r / δ := by
    intro x
    have hbase := abs_sq_mul_log_sq_le (u := f x) hδ_pos
    have hidentity : f x ^ 2 * (f x ^ 2) ^ δ = |f x| ^ r :=
      sq_mul_rpow_eq_abs_rpow hr_ge_two
    have hnorm_abs : ‖f x‖ = |f x| := Real.norm_eq_abs (f x)
    calc |f x ^ 2 * Real.log (f x ^ 2)|
        ≤ 1 + f x ^ 2 * (f x ^ 2) ^ δ / δ := hbase
      _ = 1 + |f x| ^ r / δ := by rw [hidentity]
      _ = 1 + ‖f x‖ ^ r / δ := by rw [hnorm_abs]
  -- Step 7: assemble via `Integrable.mono'`.
  refine MeasureTheory.Integrable.mono' hint_bound hint_meas ?_
  refine Filter.Eventually.of_forall (fun x => ?_)
  simpa [Real.norm_eq_abs] using h_point x

end YangMills
