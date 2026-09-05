import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# PRE-VALIDATION: isolated value-action normalization repro

Source present; .olean not materialized; result not compiler-verified.
Mathlib only, no project imports. This file is not in the running
point-probe retry queue. Run it before the later physical value-action
assembly, after preserving the current gate's evidence.

These examples test arithmetic only. They do not establish a physical
kernel bound, owner count, regional inverse, derivative B0 or contraction.
The surviving R^2 is intentional and must not be replaced by one.
-/

noncomputable section

example (R C : ℝ) (hR : R ≠ 0) :
    R ^ 4 * (C * (R ^ 2)⁻¹) = C * R ^ 2 := by
  field_simp [hR] <;> ring

example (R : ℕ) (C : ℝ) (hR : 0 < R) :
    ((R ^ 4 : ℕ) : ℝ) * (C * (((R : ℝ) ^ 2)⁻¹)) =
      C * (R : ℝ) ^ 2 := by
  have hRreal : (R : ℝ) ≠ 0 := (Nat.cast_pos.mpr hR).ne'
  rw [Nat.cast_pow]
  field_simp [hRreal] <;> ring

example (R C : ℝ) (hC : 0 ≤ C) : 0 ≤ C * (R ^ 2)⁻¹ := by
  positivity

example (N A C rate dist v : ℝ)
    (hA : A ≤ C) (hN : 0 ≤ N) (hv : 0 ≤ v) :
    N * (A * Real.exp (-(rate * dist))) * v ≤
      N * (C * Real.exp (-(rate * dist))) * v := by
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hA (Real.exp_pos _).le) hN) hv

end
