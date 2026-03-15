import Mathlib

namespace YangMills
open MeasureTheory Real Filter Set

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ## Cauchy-Schwarz and covariance lemmas
    Extracted from StroockZegarlinski.lean to break import cycles. -/

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
    -- Key: 0 ≤ ∫(B·f - I·g)² = B²A - BI²  [expand and integrate]
    have h_poly : 0 ≤ B ^ 2 * A - B * I ^ 2 := by
      have hint : Integrable (fun x => (B * f x - I * g x) ^ 2) μ :=
        (((hf2.const_mul (B ^ 2)).sub (hfg.const_mul (2 * B * I))).add
          (hg2.const_mul (I ^ 2))).congr (ae_of_all _ fun x => by ring)
      have h0 : 0 ≤ ∫ x, (B * f x - I * g x) ^ 2 ∂μ :=
        integral_nonneg fun x => sq_nonneg _
      have hcalc : ∫ x, (B * f x - I * g x) ^ 2 ∂μ = B ^ 2 * A - B * I ^ 2 := by
        rw [integral_congr_ae (ae_of_all _ fun x => show (B * f x - I * g x) ^ 2 =
            B ^ 2 * f x ^ 2 - 2 * B * I * (f x * g x) + I ^ 2 * g x ^ 2 by ring)]
        rw [integral_add ((hf2.const_mul _).sub (hfg.const_mul _)) (hg2.const_mul _)]
        rw [integral_sub (hf2.const_mul _) (hfg.const_mul _)]
        simp only [integral_const_mul]; ring
      linarith
    by_cases hB0 : B = 0
    · -- g = 0 a.e. → I = 0
      have hg_ae : g =ᵐ[μ] 0 := by
        have := (integral_eq_zero_iff_of_nonneg_ae
          (ae_of_all _ fun x => sq_nonneg (g x)) hg2).mp hB0
        filter_upwards [this] with x hx
        exact pow_eq_zero_iff (by norm_num : 2 ≠ 0) |>.mp hx
      have hI0 : I = 0 := integral_congr_ae
        (by filter_upwards [hg_ae] with x hx; simp [hx])
      simp [hI0, hB0]
    · have hB_pos : 0 < B := lt_of_le_of_ne hB_nn (Ne.symm hB0)
      -- From B²A - BI² ≥ 0: BI² ≤ B²A → I² ≤ BA = AB
      have hI2 : I ^ 2 ≤ A * B := by
        have h1 : B * I ^ 2 ≤ B ^ 2 * A := by linarith
        have h2 : I ^ 2 ≤ B * A := (mul_le_mul_left hB_pos).mp h1
        linarith [mul_comm A B]
      rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_sq_eq_abs]
      exact Real.sqrt_le_sqrt hI2 |>.trans (by
        rw [Real.sqrt_mul hA_nn])
        |>.trans_eq (by rw [Real.sqrt_mul hA_nn])
  · simp only [integral_undef hfg, zero_pow (by norm_num : 2 ≠ 0)]
    exact mul_nonneg (integral_nonneg fun x => sq_nonneg _)
                     (integral_nonneg fun x => sq_nonneg _)

/-- |∫fg| ≤ √(∫f²) · √(∫g²) — Cauchy-Schwarz for integrals. -/
private lemma abs_integral_mul_le {μ : Measure Ω}
    (f g : Ω → ℝ)
    (hf2 : Integrable (fun x => f x ^ 2) μ)
    (hg2 : Integrable (fun x => g x ^ 2) μ) :
    |∫ x, f x * g x ∂μ| ≤
    Real.sqrt (∫ x, f x ^ 2 ∂μ) * Real.sqrt (∫ x, g x ^ 2 ∂μ) := by
  rw [← Real.sqrt_mul (integral_nonneg fun x => sq_nonneg (f x)),
      ← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt (integral_mul_sq_le f g hf2 hg2)

/-- Covariance identity: ∫FG - (∫F)(∫G) = ∫(F-mF)(G-mG). -/
private lemma covariance_eq_centered {μ : Measure Ω} [IsProbabilityMeasure μ]
    (F G : Ω → ℝ) (hF : Integrable F μ) (hG : Integrable G μ)
    (hFG : Integrable (fun x => F x * G x) μ) :
    ∫ x, F x * G x ∂μ - (∫ x, F x ∂μ) * (∫ x, G x ∂μ) =
    ∫ x, (F x - ∫ y, F y ∂μ) * (G x - ∫ y, G y ∂μ) ∂μ := by
  set mF := ∫ y, F y ∂μ
  set mG := ∫ y, G y ∂μ
  rw [integral_congr_ae (ae_of_all _ fun x => show
      (F x - mF) * (G x - mG) = F x * G x - mG * F x - mF * G x + mF * mG by ring)]
  rw [integral_add ((hFG.sub (hF.const_mul mG)).sub (hG.const_mul mF))
      (integrable_const _)]
  rw [integral_sub (hFG.sub (hF.const_mul mG)) (hG.const_mul mF)]
  rw [integral_sub hFG (hF.const_mul mG)]
  simp only [integral_const_mul, integral_const, probReal_univ, smul_eq_mul, mul_one]
  ring

/-- Covariance bound: |Cov(F,G)| ≤ √Var(F) · √Var(G). Pure Cauchy-Schwarz.
    Requires Integrable (F*G) because without it, ∫(F*G)=0 by Lean convention
    but Cov(F,G) = (∫F)(∫G) ≠ 0 in general, making the bound false. -/
lemma covariance_le_sqrt_var {μ : Measure Ω} [IsProbabilityMeasure μ]
    (F G : Ω → ℝ)
    (hFv : Integrable (fun x => (F x - ∫ y, F y ∂μ) ^ 2) μ)
    (hGv : Integrable (fun x => (G x - ∫ y, G y ∂μ) ^ 2) μ)
    (hFG : Integrable (fun x => F x * G x) μ) :
    |∫ x, F x * G x ∂μ - (∫ x, F x ∂μ) * (∫ x, G x ∂μ)| ≤
    Real.sqrt (∫ x, (F x - ∫ y, F y ∂μ) ^ 2 ∂μ) *
    Real.sqrt (∫ x, (G x - ∫ y, G y ∂μ) ^ 2 ∂μ) := by
  set Fc := fun x => F x - ∫ y, F y ∂μ
  set Gc := fun x => G x - ∫ y, G y ∂μ
  have hF1 : Integrable F μ :=
    sq_sub_int_implies_int μ F (hFv.1.1.of_comp (by fun_prop)) (∫ y, F y ∂μ)
      (by simpa using hFv)
  have hG1 : Integrable G μ :=
    sq_sub_int_implies_int μ G (hGv.1.1.of_comp (by fun_prop)) (∫ y, G y ∂μ)
      (by simpa using hGv)
  rw [covariance_eq_centered F G hF1 hG1 hFG]
  exact abs_integral_mul_le Fc Gc hFv hGv


end YangMills
