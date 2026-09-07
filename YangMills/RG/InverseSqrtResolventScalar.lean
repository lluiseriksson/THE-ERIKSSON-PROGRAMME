import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.IntegralRepresentation

/-!
# Scalar majorant for the inverse-square-root resolvent integral

This module isolates the scalar integrability statement behind the
Balakrishnan comparison.  For `m > 0` it uses Mathlib's integrable
`rpowIntegrand₀₁` at exponent `1/2`, multiplied by a bounded factor.
-/

namespace YangMills.RG

open MeasureTheory Set
open scoped NNReal

/-- Integrable scalar majorant, written in a form directly consumable by
Mathlib's `rpowIntegrand₀₁` theorem. -/
noncomputable def inverseSqrtResolventScalarMajorant (m t : ℝ) : ℝ :=
  m⁻¹ * (m + t)⁻¹ * Real.rpowIntegrand₀₁ (1 / 2 : ℝ) t m

theorem integrableOn_inverseSqrtResolventScalarMajorant
    {m : ℝ} (hm : 0 < m) :
    IntegrableOn (inverseSqrtResolventScalarMajorant m) (Ioi 0) := by
  have hp : (1 / 2 : ℝ) ∈ Ioo 0 1 := by norm_num
  have hg :=
    Real.integrableOn_rpowIntegrand₀₁_Ioi hp hm.le
  let f : ℝ → ℝ := fun t => m⁻¹ * (m + t)⁻¹
  have hfmeas :
      AEStronglyMeasurable f (volume.restrict (Ioi 0)) := by
    apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioi
    apply ContinuousOn.mul continuousOn_const
    apply ContinuousOn.inv₀
    · exact continuousOn_const.add continuousOn_id
    · intro t ht
      change 0 < t at ht
      linarith
  have hfbound :
      ∀ᵐ t ∂volume.restrict (Ioi 0), ‖f t‖ ≤ m⁻¹ * m⁻¹ := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    change 0 < t at ht
    have hmt : 0 < m + t := by linarith
    rw [Real.norm_eq_abs, abs_of_pos (mul_pos (inv_pos.mpr hm) (inv_pos.mpr hmt))]
    exact mul_le_mul_of_nonneg_left
      ((inv_le_inv₀ hmt hm).2 (by linarith))
      (inv_nonneg.mpr hm.le)
  have hprod := hg.bdd_mul hfmeas hfbound
  change Integrable
    (fun t => m⁻¹ * (m + t)⁻¹ *
      Real.rpowIntegrand₀₁ (1 / 2 : ℝ) t m)
    (volume.restrict (Ioi 0))
  simpa only [f, mul_assoc] using hprod

/-- On the positive half-line, the packaged majorant is exactly
`t⁻¹ᐟ² / (m+t)²`. -/
theorem inverseSqrtResolventScalarMajorant_eq
    {m t : ℝ} (hm : 0 < m) (ht : 0 < t) :
    inverseSqrtResolventScalarMajorant m t =
      (Real.sqrt t)⁻¹ * (m + t)⁻¹ * (m + t)⁻¹ := by
  have hp : (1 / 2 : ℝ) ∈ Ioo 0 1 := by norm_num
  rw [inverseSqrtResolventScalarMajorant,
    Real.rpowIntegrand₀₁_eq_pow_div hp ht.le hm.le]
  have hpow : t ^ ((1 / 2 : ℝ) - 1) = (Real.sqrt t)⁻¹ := by
    rw [show (1 / 2 : ℝ) - 1 = -(1 / 2 : ℝ) by ring]
    rw [Real.rpow_neg ht.le, ← Real.sqrt_eq_rpow]
  rw [hpow]
  field_simp
  all_goals ring

/-- The two-margin scalar kernel occurring in the second-resolvent identity. -/
noncomputable def inverseSqrtTwoMarginScalar
    (c₀ c₁ t : ℝ) : ℝ :=
  (Real.sqrt t)⁻¹ * (c₁ + t)⁻¹ * (c₀ + t)⁻¹

/-- The two-margin scalar kernel is dominated by the common-margin majorant
with `m = min c₀ c₁`. -/
theorem inverseSqrtTwoMarginScalar_le_commonMajorant
    {c₀ c₁ t : ℝ} (hc₀ : 0 < c₀) (hc₁ : 0 < c₁) (ht : 0 < t) :
    inverseSqrtTwoMarginScalar c₀ c₁ t ≤
      inverseSqrtResolventScalarMajorant (min c₀ c₁) t := by
  have hm : 0 < min c₀ c₁ := lt_min hc₀ hc₁
  rw [inverseSqrtTwoMarginScalar,
    inverseSqrtResolventScalarMajorant_eq hm ht]
  have hsqrt : 0 ≤ (Real.sqrt t)⁻¹ :=
    inv_nonneg.mpr (Real.sqrt_nonneg t)
  have hc₁t : 0 < c₁ + t := add_pos hc₁ ht
  have hc₀t : 0 < c₀ + t := add_pos hc₀ ht
  have hmt : 0 < min c₀ c₁ + t := add_pos hm ht
  have h₁ :
      (c₁ + t)⁻¹ ≤ (min c₀ c₁ + t)⁻¹ := by
    apply (inv_le_inv₀ hc₁t hmt).2
    linarith [min_le_right c₀ c₁]
  have h₀ :
      (c₀ + t)⁻¹ ≤ (min c₀ c₁ + t)⁻¹ := by
    apply (inv_le_inv₀ hc₀t hmt).2
    linarith [min_le_left c₀ c₁]
  simpa only [mul_assoc] using
    mul_le_mul_of_nonneg_left
      (mul_le_mul h₁ h₀ (inv_nonneg.mpr hc₀t.le)
        (inv_nonneg.mpr hmt.le))
      hsqrt

/-- The scalar two-margin kernel is integrable on the positive half-line. -/
theorem integrableOn_inverseSqrtTwoMarginScalar
    {c₀ c₁ : ℝ} (hc₀ : 0 < c₀) (hc₁ : 0 < c₁) :
    IntegrableOn (inverseSqrtTwoMarginScalar c₀ c₁) (Ioi 0) := by
  have hm : 0 < min c₀ c₁ := lt_min hc₀ hc₁
  have hmajorant :=
    integrableOn_inverseSqrtResolventScalarMajorant hm
  have hmeas :
      AEStronglyMeasurable
        (inverseSqrtTwoMarginScalar c₀ c₁)
        (volume.restrict (Ioi 0)) := by
    apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioi
    apply ContinuousOn.mul
    · apply ContinuousOn.mul
      · apply ContinuousOn.inv₀
        · exact Real.continuous_sqrt.continuousOn
        · intro t ht
          exact (Real.sqrt_pos.2 ht).ne'
      · apply ContinuousOn.inv₀
        · exact continuousOn_const.add continuousOn_id
        · intro t ht
          exact (add_pos hc₁ ht).ne'
    · apply ContinuousOn.inv₀
      · exact continuousOn_const.add continuousOn_id
      · intro t ht
        exact (add_pos hc₀ ht).ne'
  refine Integrable.mono' hmajorant hmeas ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  change 0 < t at ht
  have hnonneg : 0 ≤ inverseSqrtTwoMarginScalar c₀ c₁ t := by
    exact mul_nonneg
      (mul_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg t))
        (inv_nonneg.mpr (add_pos hc₁ ht).le))
      (inv_nonneg.mpr (add_pos hc₀ ht).le)
  rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
  exact inverseSqrtTwoMarginScalar_le_commonMajorant hc₀ hc₁ ht

end YangMills.RG
