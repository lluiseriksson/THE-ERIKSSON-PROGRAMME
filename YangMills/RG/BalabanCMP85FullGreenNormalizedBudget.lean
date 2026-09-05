import Mathlib

/-!
# PRE-VALIDATION: Inverse-fourth normalization with the inverse-square scale retained.

Source present; this promoted module's `.olean` is not yet materialized,
and this promoted graph is not yet compiler-verified. The corresponding
draft passed diagnostic v3 at be4e73409ac444d23e95c2eae2584fece5882f98;
that diagnostic is not a cold seal of this module.

Only names, imports and audit placement change in this promotion. The
mathematical statements, constants and hypotheses are preserved. No
regional/derivative B0, window-15 attainment or terminal obligation is claimed.
-/

namespace YangMills.RG.CMP85FullGreenNormalizedBudget

theorem split {r C D : ℝ} (hr : 1 ≤ r) (hD : 0 ≤ D) :
    (r ^ 4)⁻¹ * (C + D * (r + 1) ^ 2) ≤
      (r ^ 4)⁻¹ * C + 4 * D * (r ^ 2)⁻¹ := by
  have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hp : (r + 1) ^ 2 ≤ 4 * r ^ 2 := by
    have hprod := mul_nonneg (sub_nonneg.mpr hr)
      (show 0 ≤ 3 * r + 1 by linarith)
    nlinarith
  have hs := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left hp hD)
    (inv_nonneg.mpr (pow_nonneg hr0.le 4))
  calc
    _ = (r ^ 4)⁻¹ * C + (r ^ 4)⁻¹ * (D * (r + 1) ^ 2) := by ring
    _ ≤ (r ^ 4)⁻¹ * C + (r ^ 4)⁻¹ * (D * (4 * r ^ 2)) :=
      add_le_add (le_refl _) hs
    _ = _ := by field_simp [ne_of_gt hr0] <;> ring

theorem retain_inverse_square {r C D : ℝ}
    (hr : 1 ≤ r) (hC : 0 ≤ C) (hD : 0 ≤ D) :
    (r ^ 4)⁻¹ * (C + D * (r + 1) ^ 2) ≤
      (C + 4 * D) * (r ^ 2)⁻¹ := by
  have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hp : (r + 1) ^ 2 ≤ 4 * r ^ 2 := by
    have hprod := mul_nonneg (sub_nonneg.mpr hr)
      (show 0 ≤ 3 * r + 1 by linarith)
    nlinarith
  have hsq : 1 ≤ r ^ 2 := by nlinarith
  have hcr : C ≤ C * r ^ 2 := by
    nlinarith [mul_nonneg hC (sub_nonneg.mpr hsq)]
  have hnum : C + D * (r + 1) ^ 2 ≤ (C + 4 * D) * r ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hp hD]
  calc
    _ ≤ (r ^ 4)⁻¹ * ((C + 4 * D) * r ^ 2) :=
      mul_le_mul_of_nonneg_left hnum (inv_nonneg.mpr (pow_nonneg hr0.le 4))
    _ = _ := by field_simp [ne_of_gt hr0] <;> ring


end YangMills.RG.CMP85FullGreenNormalizedBudget
