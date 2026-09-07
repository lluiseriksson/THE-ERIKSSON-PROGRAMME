import Mathlib

/-! PRE-VALIDATION: source present; .olean not materialized and compiler
verification pending. Scalar normalizations only, before the physical draft. -/

noncomputable section

example (B a : ℝ) (d : ℕ) (hB : B ≠ 0) :
    a * (B * B⁻¹) ^ (d - 2) / (B⁻¹) ^ d = a * B ^ d := by
  rw [mul_inv_cancel₀ hB]
  simp only [one_pow, mul_one, inv_pow, div_inv_eq_mul]

example (B a : ℝ) (d : ℕ) (hB : B ≠ 0) :
    (a * B ^ d) * ((B ^ d)⁻¹) ^ 2 = a * (B ^ d)⁻¹ := by
  have hBd : B ^ d ≠ 0 := pow_ne_zero d hB
  field_simp [hBd]
  <;> ring

end
