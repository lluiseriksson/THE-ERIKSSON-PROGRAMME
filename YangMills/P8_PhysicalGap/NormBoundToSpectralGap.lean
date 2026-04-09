import Mathlib
import YangMills.P8_PhysicalGap.DiscreteSpectralGap
import YangMills.P8_PhysicalGap.StateNormBoundLemmas

namespace YangMills

open ContinuousLinearMap Real

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]

private lemma proj_pow_eq (P₀ : H →L[ℝ] H) (hP₀_idem : P₀ * P₀ = P₀) :
    ∀ n : ℕ, P₀ ^ (n + 1) = P₀ := by
  intro n
  induction n with
  | zero => simp [pow_one]
  | succ n ih => rw [pow_succ, ih, hP₀_idem]

theorem spectralGap_of_norm_le
    (T P₀ : H →L[ℝ] H)
    (hP₀_idem : P₀ * P₀ = P₀)
    (hTP : T * P₀ = P₀)
    (hPT : P₀ * T = P₀)
    (lam : ℝ) (hlam0 : 0 < lam) (hlam1 : lam < 1)
    (hbound : ‖T - P₀‖ ≤ lam) :
    HasSpectralGap T P₀ (- Real.log lam) (‖(1 : H →L[ℝ] H) - P₀‖ + 1) := by
  by_cases h0 : ‖T - P₀‖ = 0
  · have hT_eq : T = P₀ := sub_eq_zero.mp (norm_eq_zero.mp h0)
    rw [hT_eq]
    have hgam_pos : 0 < - Real.log lam := neg_pos.mpr (Real.log_neg hlam0 hlam1)
    have hC_pos : 0 < ‖(1 : H →L[ℝ] H) - P₀‖ + 1 := by positivity
    refine ⟨hgam_pos, hC_pos, ?_⟩
    intro n
    rcases n with _ | m
    · simp only [pow_zero, Nat.cast_zero, mul_zero, Real.exp_zero, mul_one]
      exact le_add_of_nonneg_right one_pos.le
    · have hpow : P₀ ^ (m + 1) = P₀ := proj_pow_eq P₀ hP₀_idem m
      have hval : ‖P₀ ^ (m + 1) - P₀‖ = 0 := by rw [hpow, sub_self, norm_zero]
      rw [hval]; positivity
  · have hpos : 0 < ‖T - P₀‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
    have hT_lt_1 : ‖T - P₀‖ < 1 := lt_of_le_of_lt hbound hlam1
    have hgap85 : HasSpectralGap T P₀ (- Real.log ‖T - P₀‖) (‖(1 : H →L[ℝ] H) - P₀‖ + 1) :=
      spectralGap_of_normContraction T P₀ hP₀_idem hTP hPT hpos hT_lt_1
    have hgam_pos : 0 < - Real.log lam := neg_pos.mpr (Real.log_neg hlam0 hlam1)
    have hlog_le : Real.log ‖T - P₀‖ ≤ Real.log lam :=
      Real.log_le_log hpos hbound
    refine ⟨hgam_pos, hgap85.2.1, fun n => ?_⟩
    have h85 := hgap85.2.2 n
    have hnn : (0 : ℝ) ≤ ↑n := Nat.cast_nonneg n
    have hexp : Real.exp (-(- Real.log ‖T - P₀‖) * ↑n) ≤
        Real.exp (-(- Real.log lam) * ↑n) := by
      apply Real.exp_le_exp.mpr; nlinarith
    linarith [mul_le_mul_of_nonneg_left hexp (le_of_lt hgap85.2.1)]

theorem spectralGap_of_normContraction_via_le
    (T P₀ : H →L[ℝ] H)
    (hP₀_idem : P₀ * P₀ = P₀)
    (hTP : T * P₀ = P₀)
    (hPT : P₀ * T = P₀)
    (hla0 : 0 < ‖T - P₀‖)
    (hla1 : ‖T - P₀‖ < 1) :
    HasSpectralGap T P₀ (- Real.log ‖T - P₀‖) (‖(1 : H →L[ℝ] H) - P₀‖ + 1) :=
  spectralGap_of_norm_le T P₀ hP₀_idem hTP hPT ‖T - P₀‖ hla0 hla1 (le_refl _)

end YangMills
