import Mathlib

/-!
Project-free algebraic repro only. PRE-VALIDATION until its own Colab exit.
This does not instantiate any physical coefficient or source-flow window.
-/

namespace FullGreenNormalizedBudgetRepro

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
      add_le_add_left hs _
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

#print axioms split
#print axioms retain_inverse_square

end FullGreenNormalizedBudgetRepro
