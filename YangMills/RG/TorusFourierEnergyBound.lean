import YangMills.RG.TorusCountingParseval

/-! Quantitative bounds derived for the actual centered characters.
Integer lifts avoid using the wrapped ZMod.val as a small frequency.
The physical real-cochain identification remains separate. -/

namespace YangMills.RG

open scoped BigOperators

variable {d n : ℕ} [NeZero n]

theorem stdAddChar_centered_bound (R : ℕ) (k : Fin (2 * R + 1)) :
    ‖ZMod.stdAddChar (((k.val : ℕ) : ZMod n) - (R : ZMod n)) - 1‖ ≤
      2 * Real.pi * (R : ℝ) / (n : ℝ) := by
  let z : ℤ := (k.val : ℤ) - (R : ℤ)
  have hz : |(z : ℝ)| ≤ (R : ℝ) := by
    have hk : (k.val : ℝ) ≤ 2 * (R : ℝ) := by
      exact_mod_cast (Nat.le_of_lt_succ k.isLt)
    have hk0 : (0 : ℝ) ≤ k.val := Nat.cast_nonneg _
    dsimp [z]
    push_cast
    apply abs_le.mpr
    constructor <;> linarith
  have hn : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have hp : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  have hcast : ((k.val : ZMod n) - (R : ZMod n)) = (z : ZMod n) := by
    simp [z]
  rw [hcast, ZMod.stdAddChar_coe]
  have he : (2 * (Real.pi : ℂ) * Complex.I * (z : ℂ) / (n : ℂ)) =
      Complex.I * ((2 * Real.pi * (z : ℝ) / (n : ℝ) : ℝ) : ℂ) := by
    push_cast
    ring
  rw [he]
  calc
    _ ≤ ‖2 * Real.pi * (z : ℝ) / (n : ℝ)‖ := Real.norm_exp_I_mul_ofReal_sub_one_le
    _ = 2 * Real.pi * |(z : ℝ)| / (n : ℝ) := by
      rw [Real.norm_eq_abs, abs_div, abs_mul, abs_of_nonneg hp, abs_of_pos hn]
    _ ≤ _ := (div_le_div_iff_of_pos_right hn).mpr (mul_le_mul_of_nonneg_left hz hp)

theorem centeredFourier_coordinate_multiplier_bound (R : ℕ)
    (k : Fin d → Fin (2 * R + 1)) (j : Fin d) :
    ‖centeredFourierProfile (d := d) (n := n) R k
      (Pi.single j (1 : ZMod n)) - 1‖ ≤ 2 * Real.pi * (R : ℝ) / (n : ℝ) := by
  classical
  simpa [centeredFourierProfile, torusFourierCharacter,
    centeredFourierFrequency, Pi.single_apply] using
    (stdAddChar_centered_bound (n := n) R (k j))

theorem centeredFourier_multiplier_sum_sq_le (R : ℕ)
    (k : Fin d → Fin (2 * R + 1)) :
    (∑ j : Fin d, ‖centeredFourierProfile (d := d) (n := n) R k
      (Pi.single j (1 : ZMod n)) - 1‖ ^ 2) ≤
      (d : ℝ) * (2 * Real.pi * (R : ℝ) / (n : ℝ)) ^ 2 := by
  classical
  calc
    _ ≤ ∑ j : Fin d, (2 * Real.pi * (R : ℝ) / (n : ℝ)) ^ 2 := by
      apply Finset.sum_le_sum
      intro j hj
      have h := centeredFourier_coordinate_multiplier_bound (n := n) R k j
      have ha := norm_nonneg (centeredFourierProfile (d := d) (n := n) R k
        (Pi.single j (1 : ZMod n)) - 1)
      have hb : (0 : ℝ) ≤ 2 * Real.pi * (R : ℝ) / (n : ℝ) := by positivity
      nlinarith [mul_nonneg (sub_nonneg.mpr h) (add_nonneg hb ha)]
    _ = _ := by simp

theorem centeredFourier_stencilEnergy_le (R : ℕ) (hR : 2 * R < n)
    (c : (Fin d → Fin (2 * R + 1)) → ℂ) (j : Fin d) :
    oneComponentStencilEnergy
      (fun x => ∑ k, c k * centeredFourierProfile (d := d) (n := n) R k x)
      (fun t => Pi.single t (1 : ZMod n)) j ≤
      (4 * Real.pi ^ 2 * (d : ℝ) * (R : ℝ) ^ 2 / (n : ℝ) ^ 2) *
        countingL2Mass (fun x => ∑ k, c k * centeredFourierProfile (d := d) (n := n) R k x) := by
  classical
  rw [centeredFourier_stencilEnergy R hR, centeredFourier_counting_mass R hR]
  have hb : (d : ℝ) * (2 * Real.pi * (R : ℝ) / (n : ℝ)) ^ 2 =
      4 * Real.pi ^ 2 * (d : ℝ) * (R : ℝ) ^ 2 / (n : ℝ) ^ 2 := by
    rw [div_pow]
    ring
  calc
    _ ≤ (n ^ d : ℝ) * ∑ k, ‖c k‖ ^ 2 *
        ((d : ℝ) * (2 * Real.pi * (R : ℝ) / (n : ℝ)) ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.sum_le_sum
      intro k hk
      exact mul_le_mul_of_nonneg_left (centeredFourier_multiplier_sum_sq_le R k) (sq_nonneg _)
    _ = _ := by
      rw [hb, ← Finset.sum_mul]
      ring

end YangMills.RG
