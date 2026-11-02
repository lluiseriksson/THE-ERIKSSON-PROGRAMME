import Mathlib

/-! Prepared, not compiled: the coefficient-level weighted path step for the
internal-resistance block-observation route. No Poincare certificate is assumed.
The product partition, variance tensorization and actual field adapter remain
separate construction obligations. Compile only in this chat's own Colab Linux. -/
namespace YangMills.RG
open scoped BigOperators
set_option maxHeartbeats 1800000

/-- An explicit scalar square completion, retaining coefficient positivity. -/
theorem internalResistance_square_completion (a v z : ℝ) (ha : 0 < a) :
    0 ≤ a * v^2 - 2 * z * v + z^2 / a := by
  have hid : a * (v - z / a)^2 = a * v^2 - 2 * z * v + z^2 / a := by
    field_simp [ne_of_gt ha]
    <;> ring
  rw [← hid]
  exact mul_nonneg ha.le (sq_nonneg _)

/-- Weighted Cauchy-Schwarz derived from positive coefficients, including an
empty index set. The inverse-conductance sum is the actual finite sum. -/
theorem internalResistance_scalar_sum {ι : Type*} (s : Finset ι)
    (a v : ι → ℝ) (ha : ∀ i ∈ s, 0 < a i) :
    (∑ i ∈ s, v i)^2 ≤ (∑ i ∈ s, (a i)⁻¹) * (∑ i ∈ s, a i * (v i)^2) := by
  classical
  by_cases hs : s.Nonempty
  · let S : ℝ := ∑ i ∈ s, (a i)⁻¹
    let T : ℝ := ∑ i ∈ s, v i
    let E : ℝ := ∑ i ∈ s, a i * (v i)^2
    obtain ⟨i, hi⟩ := hs
    have hS : 0 < S := lt_of_lt_of_le (inv_pos.mpr (ha i hi))
      (Finset.single_le_sum (fun j hj => (inv_pos.mpr (ha j hj)).le) hi)
    have hquad (z : ℝ) : 0 ≤ E - 2 * z * T + z^2 * S := by
      dsimp [E, T, S]
      simpa only [div_eq_mul_inv, Finset.sum_add_distrib,
        Finset.sum_sub_distrib, Finset.mul_sum] using
        (Finset.sum_nonneg (fun j hj =>
          internalResistance_square_completion (a j) (v j) z (ha j hj)))
    have hq := mul_nonneg hS.le (hquad (T / S))
    have hid : S * (E - 2 * (T / S) * T + (T / S)^2 * S) = S * E - T^2 := by
      field_simp [ne_of_gt hS]
      <;> ring
    rw [hid] at hq
    change T^2 ≤ S * E
    linarith
  · have he : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    subst s
    simp

/-- Vector-valued weighted sum inequality, using the actual normed sum. -/
theorem internalResistance_norm_sum {ι V : Type*} [NormedAddCommGroup V]
    (s : Finset ι) (a : ι → ℝ) (v : ι → V) (ha : ∀ i ∈ s, 0 < a i) :
    ‖∑ i ∈ s, v i‖^2 ≤
      (∑ i ∈ s, (a i)⁻¹) * (∑ i ∈ s, a i * ‖v i‖^2) := by
  classical
  have hn : ‖∑ i ∈ s, v i‖ ≤ ∑ i ∈ s, ‖v i‖ := norm_sum_le _ _
  have hsq := pow_le_pow_left₀ (norm_nonneg (∑ i ∈ s, v i)) hn 2
  exact hsq.trans (internalResistance_scalar_sum s a (fun i => ‖v i‖) ha)

/-- Telescope on the actual finite interval, without an assumed path witness. -/
theorem internalResistance_telescope {V : Type*} [AddCommGroup V]
    (u : ℕ → V) (n : ℕ) :
    (∑ i ∈ Finset.range n, (u (i + 1) - u i)) = u n - u 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      abel

/-- The actual endpoint difference is bounded by the actual series resistance
and actual internal weighted energy. The length-zero case is included. -/
theorem internalResistance_path {V : Type*} [NormedAddCommGroup V]
    (u : ℕ → V) (a : ℕ → ℝ) (n : ℕ)
    (ha : ∀ i ∈ Finset.range n, 0 < a i) :
    ‖u n - u 0‖^2 ≤ (∑ i ∈ Finset.range n, (a i)⁻¹) *
      (∑ i ∈ Finset.range n, a i * ‖u (i + 1) - u i‖^2) := by
  have h := internalResistance_norm_sum (Finset.range n) a
    (fun i => u (i + 1) - u i) ha
  rw [internalResistance_telescope] at h
  exact h

end YangMills.RG