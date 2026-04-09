import Mathlib
import YangMills.P8_PhysicalGap.StateNormBoundLemmas

namespace YangMills

open ContinuousLinearMap Real

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]

private lemma res_mul_proj_zero
    {T P₀ : H →L[ℝ] H} (hTP : T * P₀ = P₀) (hP₀ : P₀ * P₀ = P₀) :
    (T - P₀) * P₀ = 0 := by
  rw [sub_mul, hTP, hP₀, sub_self]

private lemma res_pow_mul_proj_zero
    {T P₀ : H →L[ℝ] H} (hTP : T * P₀ = P₀) (hP₀ : P₀ * P₀ = P₀) (n : ℕ) :
    (T - P₀) ^ (n + 1) * P₀ = 0 := by
  rw [pow_succ, mul_assoc, res_mul_proj_zero hTP hP₀, mul_zero]

private lemma T_pow_decomp
    {T P₀ : H →L[ℝ] H} (hP₀ : P₀ * P₀ = P₀) (hTP : T * P₀ = P₀) (hPT : P₀ * T = P₀) :
    ∀ n : ℕ, T ^ (n + 1) = P₀ + (T - P₀) ^ (n + 1) := by
  intro n
  induction n with
  | zero =>
    simp only [pow_succ, pow_zero, one_mul]
    abel
  | succ k ih =>
    rw [pow_succ T, pow_succ (T - P₀), ih]
    have h0 : (T - P₀) ^ (k + 1) * P₀ = 0 := res_pow_mul_proj_zero hTP hP₀ k
    have key : (T - P₀) ^ (k + 1) * T = (T - P₀) ^ (k + 1) * (T - P₀) :=
      calc (T - P₀) ^ (k + 1) * T
          = (T - P₀) ^ (k + 1) * ((T - P₀) + P₀) := by congr 1; abel
        _ = (T - P₀) ^ (k + 1) * (T - P₀) + (T - P₀) ^ (k + 1) * P₀ := by rw [mul_add]
        _ = (T - P₀) ^ (k + 1) * (T - P₀) + 0 := by rw [h0]
        _ = (T - P₀) ^ (k + 1) * (T - P₀) := by rw [add_zero]
    rw [add_mul, hPT, key]

/-- ‖f ^ (n + 1)‖ ≤ ‖f‖ ^ (n + 1) for ContinuousLinearMaps. -/
private lemma clm_norm_pow_le (f : H →L[ℝ] H) (n : ℕ) :
    ‖f ^ (n + 1)‖ ≤ ‖f‖ ^ (n + 1) := by
  induction n with
  | zero => simp [pow_one]
  | succ k ihk =>
    rw [pow_succ, pow_succ]
    exact le_trans (norm_mul_le _ _) (mul_le_mul_of_nonneg_right ihk (norm_nonneg _))

theorem spectralGap_of_normContraction
    (T P₀ : H →L[ℝ] H)
    (hP₀_idem : P₀ * P₀ = P₀)
    (hTP : T * P₀ = P₀)
    (hPT : P₀ * T = P₀)
    (hpos : 0 < ‖T - P₀‖)
    (hT_lt_1 : ‖T - P₀‖ < 1) :
    HasSpectralGap T P₀ (- Real.log ‖T - P₀‖) (‖(1 : H →L[ℝ] H) - P₀‖ + 1) := by
  have hγ_pos : 0 < - Real.log ‖T - P₀‖ :=
    neg_pos.mpr (Real.log_neg hpos hT_lt_1)
  have hC_pos : 0 < ‖(1 : H →L[ℝ] H) - P₀‖ + 1 := by positivity
  refine ⟨hγ_pos, hC_pos, ?_⟩
  intro n
  match n with
  | 0 =>
    simp only [pow_zero, Nat.cast_zero, mul_zero, Real.exp_zero, mul_one]
    exact le_add_of_nonneg_right one_pos.le
  | n + 1 =>
    have hdecomp : T ^ (n + 1) - P₀ = (T - P₀) ^ (n + 1) := by
      rw [T_pow_decomp hP₀_idem hTP hPT n]; abel
    have hnorm : ‖(T - P₀) ^ (n + 1)‖ ≤ ‖T - P₀‖ ^ (n + 1) :=
      clm_norm_pow_le (T - P₀) n
    have hexp_eq : ‖T - P₀‖ ^ (n + 1) =
        Real.exp (-(- Real.log ‖T - P₀‖) * ↑(n + 1)) := by
      rw [neg_neg, mul_comm, ← Real.log_pow]
      exact (Real.exp_log (pow_pos hpos _)).symm
    have hC_ge_one : 1 ≤ ‖(1 : H →L[ℝ] H) - P₀‖ + 1 :=
      le_add_of_nonneg_left (norm_nonneg _)
    calc ‖T ^ (n + 1) - P₀‖
        = ‖(T - P₀) ^ (n + 1)‖ := by rw [hdecomp]
      _ ≤ ‖T - P₀‖ ^ (n + 1) := hnorm
      _ = Real.exp (-(- Real.log ‖T - P₀‖) * ↑(n + 1)) := hexp_eq
      _ ≤ (‖(1 : H →L[ℝ] H) - P₀‖ + 1) *
            Real.exp (-(- Real.log ‖T - P₀‖) * ↑(n + 1)) :=
            le_mul_of_one_le_left (Real.exp_pos _).le hC_ge_one

end YangMills
