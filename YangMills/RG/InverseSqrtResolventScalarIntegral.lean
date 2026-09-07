import YangMills.RG.InverseSqrtResolventScalar
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Exact scalar Balakrishnan integral

This module evaluates the scalar integral used by the inverse-square-root
resolvent formula:

`∫₀∞ t⁻¹ᐟ² (λ+t)⁻¹ dt = π / √λ`, for `λ > 0`.

The normalization is obtained from the substitution `t = x²` and the exact
half-line arctangent integral.  The general positive `λ` statement is then
derived from Mathlib's scaling theorem for `rpowIntegrand₀₁`.
-/

namespace YangMills.RG

open MeasureTheory Set

noncomputable section

/-- The scalar inverse-square-root resolvent integrand. -/
noncomputable def inverseSqrtResolventScalarIntegrand
    (lam t : ℝ) : ℝ :=
  (Real.sqrt t)⁻¹ * (lam + t)⁻¹

/-- The scalar inverse-square-root resolvent integrand is absolutely
integrable on the positive half-line at every positive spectral value. -/
theorem integrableOn_inverseSqrtResolventScalarIntegrand
    {lam : ℝ} (hlam : 0 < lam) :
    IntegrableOn (inverseSqrtResolventScalarIntegrand lam) (Ioi 0) := by
  have hp : (1 / 2 : ℝ) ∈ Ioo 0 1 := by norm_num
  have hpoint :
      EqOn
        (inverseSqrtResolventScalarIntegrand lam)
        (fun t =>
          lam⁻¹ * Real.rpowIntegrand₀₁ (1 / 2 : ℝ) t lam)
        (Ioi 0) := by
    intro t ht
    change 0 < t at ht
    change
      (Real.sqrt t)⁻¹ * (lam + t)⁻¹ =
        lam⁻¹ * Real.rpowIntegrand₀₁ (1 / 2 : ℝ) t lam
    rw [Real.rpowIntegrand₀₁_eq_pow_div hp ht.le hlam.le]
    have hpow :
        t ^ ((1 / 2 : ℝ) - 1) = (Real.sqrt t)⁻¹ := by
      rw [show (1 / 2 : ℝ) - 1 = -(1 / 2 : ℝ) by ring]
      rw [Real.rpow_neg ht.le, ← Real.sqrt_eq_rpow]
    rw [hpow]
    field_simp
    ring
  rw [integrableOn_congr_fun hpoint measurableSet_Ioi]
  exact
    (Real.integrableOn_rpowIntegrand₀₁_Ioi hp hlam.le).const_mul lam⁻¹

/-- At unit spectral value, the scalar Balakrishnan integral equals `π`. -/
theorem integral_inverseSqrtResolventScalarIntegrand_one :
    (∫ t in Ioi 0, inverseSqrtResolventScalarIntegrand 1 t) =
      Real.pi := by
  let g : ℝ → ℝ :=
    fun t => inverseSqrtResolventScalarIntegrand 1 t
  have hsub :=
    integral_comp_rpow_Ioi_of_pos (g := g) (show (0 : ℝ) < 2 by norm_num)
  have hleft :
      (∫ x in Ioi 0,
        ((2 : ℝ) * x ^ ((2 : ℝ) - 1)) • g (x ^ (2 : ℝ))) =
        ∫ x in Ioi 0, 2 * (1 + x ^ 2)⁻¹ := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    change 0 < x at hx
    simp only [g, inverseSqrtResolventScalarIntegrand, smul_eq_mul]
    rw [show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one,
      Real.rpow_two, Real.sqrt_sq_eq_abs, abs_of_pos hx]
    field_simp
  calc
    (∫ t in Ioi 0, inverseSqrtResolventScalarIntegrand 1 t) =
        ∫ x in Ioi 0,
          ((2 : ℝ) * x ^ ((2 : ℝ) - 1)) • g (x ^ (2 : ℝ)) := by
      simpa [g] using hsub.symm
    _ = ∫ x in Ioi 0, 2 * (1 + x ^ 2)⁻¹ :=
      hleft
    _ = 2 * ∫ x in Ioi 0, (1 + x ^ 2)⁻¹ := by
      rw [← integral_const_mul]
    _ = Real.pi := by
      rw [integral_Ioi_inv_one_add_sq]
      simp
      ring

/-- Exact scalar Balakrishnan integral at every positive spectral value. -/
theorem integral_inverseSqrtResolventScalarIntegrand
    {lam : ℝ} (hlam : 0 < lam) :
    (∫ t in Ioi 0, inverseSqrtResolventScalarIntegrand lam t) =
      Real.pi * (Real.sqrt lam)⁻¹ := by
  have hp : (1 / 2 : ℝ) ∈ Ioo 0 1 := by norm_num
  have hpoint :
      EqOn
        (inverseSqrtResolventScalarIntegrand lam)
        (fun t =>
          lam⁻¹ * Real.rpowIntegrand₀₁ (1 / 2 : ℝ) t lam)
        (Ioi 0) := by
    intro t ht
    change 0 < t at ht
    change
      (Real.sqrt t)⁻¹ * (lam + t)⁻¹ =
        lam⁻¹ * Real.rpowIntegrand₀₁ (1 / 2 : ℝ) t lam
    rw [
      Real.rpowIntegrand₀₁_eq_pow_div hp ht.le hlam.le]
    have hpow :
        t ^ ((1 / 2 : ℝ) - 1) = (Real.sqrt t)⁻¹ := by
      rw [show (1 / 2 : ℝ) - 1 = -(1 / 2 : ℝ) by ring]
      rw [Real.rpow_neg ht.le, ← Real.sqrt_eq_rpow]
    rw [hpow]
    field_simp
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi hpoint]
  rw [integral_const_mul]
  rw [Real.integral_rpowIntegrand₀₁_eq_rpow_mul_const hp hlam.le]
  have hone :
      (∫ t in Ioi 0,
        Real.rpowIntegrand₀₁ (1 / 2 : ℝ) t 1) =
        Real.pi := by
    rw [← integral_inverseSqrtResolventScalarIntegrand_one]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    change 0 < t at ht
    change
      Real.rpowIntegrand₀₁ (1 / 2 : ℝ) t 1 =
        (Real.sqrt t)⁻¹ * (1 + t)⁻¹
    rw [
      Real.rpowIntegrand₀₁_eq_pow_div hp ht.le zero_le_one]
    have hpow :
        t ^ ((1 / 2 : ℝ) - 1) = (Real.sqrt t)⁻¹ := by
      rw [show (1 / 2 : ℝ) - 1 = -(1 / 2 : ℝ) by ring]
      rw [Real.rpow_neg ht.le, ← Real.sqrt_eq_rpow]
    rw [hpow]
    field_simp
    ring
  rw [hone]
  rw [← Real.sqrt_eq_rpow]
  field_simp [Real.sqrt_ne_zero'.mpr hlam]
  exact Real.sq_sqrt hlam.le

end

end YangMills.RG
