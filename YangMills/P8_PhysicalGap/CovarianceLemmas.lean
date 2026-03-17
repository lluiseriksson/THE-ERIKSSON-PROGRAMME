import Mathlib

namespace YangMills
open MeasureTheory Real Filter Set

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ## Cauchy-Schwarz and covariance lemmas — v0.8.30 -/

private lemma integral_mul_sq_le {μ : Measure Ω}
    (f g : Ω → ℝ)
    (hf2 : Integrable (fun x => f x ^ 2) μ)
    (hg2 : Integrable (fun x => g x ^ 2) μ) :
    (∫ x, f x * g x ∂μ) ^ 2 ≤
    (∫ x, f x ^ 2 ∂μ) * (∫ x, g x ^ 2 ∂μ) := by
  by_cases hfg : Integrable (fun x => f x * g x) μ
  · set A := ∫ x, f x ^ 2 ∂μ
    set B := ∫ x, g x ^ 2 ∂μ
    set I := ∫ x, f x * g x ∂μ
    have hA_nn : 0 ≤ A := integral_nonneg fun x => sq_nonneg _
    have hB_nn : 0 ≤ B := integral_nonneg fun x => sq_nonneg _
    have h_poly : 0 ≤ B ^ 2 * A - B * I ^ 2 := by
      have h0 : 0 ≤ ∫ x, (B * f x - I * g x) ^ 2 ∂μ :=
        integral_nonneg fun x => sq_nonneg _
      have h1 : Integrable (fun x => B ^ 2 * f x ^ 2) μ := hf2.const_mul _
      have h2 : Integrable (fun x => 2 * B * I * (f x * g x)) μ := hfg.const_mul _
      have h3 : Integrable (fun x => I ^ 2 * g x ^ 2) μ := hg2.const_mul _
      have h12 : Integrable (fun x => B ^ 2 * f x ^ 2 - 2 * B * I * (f x * g x)) μ :=
        h1.sub h2
      have hcalc : ∫ x, (B * f x - I * g x) ^ 2 ∂μ = B ^ 2 * A - B * I ^ 2 := by
        rw [show ∫ x, (B * f x - I * g x) ^ 2 ∂μ =
            ∫ x, ((B ^ 2 * f x ^ 2 - 2 * B * I * (f x * g x)) + I ^ 2 * g x ^ 2) ∂μ from
          integral_congr_ae (ae_of_all _ fun x => by ring)]
        rw [integral_add h12 h3, integral_sub h1 h2,
            integral_const_mul, integral_const_mul, integral_const_mul]
        ring
      linarith
    by_cases hB0 : B = 0
    · have hg_ae : ∀ᵐ x ∂μ, g x = 0 := by
        have hg2_zero : ∀ᵐ x ∂μ, g x ^ 2 = 0 :=
          (integral_eq_zero_iff_of_nonneg_ae
            (ae_of_all _ fun x => sq_nonneg (g x)) hg2).mp hB0
        filter_upwards [hg2_zero] with x hx
        exact_mod_cast pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hx
      have hI0 : I = 0 := by
        have : (fun x => f x * g x) =ᵐ[μ] (fun _ => (0 : ℝ)) := by
          filter_upwards [hg_ae] with x hx; simp [hx]
        simp [I, integral_congr_ae this]
      simp [hI0, hB0]
    · have hB_pos : 0 < B := lt_of_le_of_ne hB_nn (Ne.symm hB0)
      have hI2 : I ^ 2 ≤ A * B := by
        have h1 : B * I ^ 2 ≤ B ^ 2 * A := by linarith
        nlinarith [sq_nonneg B, mul_comm A B]
      exact hI2
  · simp only [integral_undef hfg, zero_pow (by norm_num : 2 ≠ 0)]
    exact mul_nonneg (integral_nonneg fun x => sq_nonneg _)
                     (integral_nonneg fun x => sq_nonneg _)

private lemma abs_integral_mul_le {μ : Measure Ω}
    (f g : Ω → ℝ)
    (hf2 : Integrable (fun x => f x ^ 2) μ)
    (hg2 : Integrable (fun x => g x ^ 2) μ) :
    |∫ x, f x * g x ∂μ| ≤
    Real.sqrt (∫ x, f x ^ 2 ∂μ) * Real.sqrt (∫ x, g x ^ 2 ∂μ) := by
  rw [← Real.sqrt_mul (integral_nonneg fun x => sq_nonneg (f x)),
      ← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt (integral_mul_sq_le f g hf2 hg2)

private lemma covariance_eq_centered {μ : Measure Ω} [IsProbabilityMeasure μ]
    (F G : Ω → ℝ) (hF : Integrable F μ) (hG : Integrable G μ)
    (hFG : Integrable (fun x => F x * G x) μ) :
    ∫ x, F x * G x ∂μ - (∫ x, F x ∂μ) * (∫ x, G x ∂μ) =
    ∫ x, (F x - ∫ y, F y ∂μ) * (G x - ∫ y, G y ∂μ) ∂μ := by
  set mF := ∫ y, F y ∂μ
  set mG := ∫ y, G y ∂μ
  have h1 : Integrable (fun x => F x * G x - mG * F x) μ := hFG.sub (hF.const_mul mG)
  have h2 : Integrable (fun x => mF * G x) μ := hG.const_mul mF
  have h12 : Integrable (fun x => F x * G x - mG * F x - mF * G x) μ := h1.sub h2
  have hkey : ∫ x, (F x - mF) * (G x - mG) ∂μ =
      ∫ x, F x * G x ∂μ - (∫ x, F x ∂μ) * (∫ x, G x ∂μ) := by
    have hexp : ∫ x, (F x - mF) * (G x - mG) ∂μ =
        ∫ x, (F x * G x - mG * F x - mF * G x + mF * mG) ∂μ :=
      integral_congr_ae (ae_of_all _ fun x => by ring)
    rw [hexp]
    have hsplit : ∫ x, (F x * G x - mG * F x - mF * G x + mF * mG) ∂μ =
        ∫ x, (F x * G x - mG * F x - mF * G x) ∂μ + mF * mG := by
      rw [show (fun x => F x * G x - mG * F x - mF * G x + mF * mG) =
          (fun x => (F x * G x - mG * F x - mF * G x) + mF * mG) from
        funext fun x => by ring]
      rw [integral_add h12 (integrable_const _)]
      simp [integral_const, measure_univ]
    rw [hsplit]
    have hd1 : ∫ x, (F x * G x - mG * F x - mF * G x) ∂μ =
        ∫ x, F x * G x ∂μ - mG * mF - mF * ∫ x, G x ∂μ := by
      rw [show (fun x => F x * G x - mG * F x - mF * G x) =
          (fun x => (F x * G x - mG * F x) - mF * G x) from funext fun x => by ring]
      rw [integral_sub h1 h2, integral_sub hFG (hF.const_mul mG),
          integral_const_mul, integral_const_mul]
    rw [hd1]
    simp [mF, mG]
    ring
  linarith [hkey]

/-- Covariance bound: |Cov(F,G)| ≤ √Var(F) · √Var(G) — v0.8.30.
    Takes Integrable F/G explicitly (eliminates phantom sq_sub_int_implies_int). -/
lemma covariance_le_sqrt_var {μ : Measure Ω} [IsProbabilityMeasure μ]
    (F G : Ω → ℝ)
    (hF : Integrable F μ) (hG : Integrable G μ)
    (hFv : Integrable (fun x => (F x - ∫ y, F y ∂μ) ^ 2) μ)
    (hGv : Integrable (fun x => (G x - ∫ y, G y ∂μ) ^ 2) μ)
    (hFG : Integrable (fun x => F x * G x) μ) :
    |∫ x, F x * G x ∂μ - (∫ x, F x ∂μ) * (∫ x, G x ∂μ)| ≤
    Real.sqrt (∫ x, (F x - ∫ y, F y ∂μ) ^ 2 ∂μ) *
    Real.sqrt (∫ x, (G x - ∫ y, G y ∂μ) ^ 2 ∂μ) := by
  rw [covariance_eq_centered F G hF hG hFG]
  exact abs_integral_mul_le _ _ hFv hGv

end YangMills
