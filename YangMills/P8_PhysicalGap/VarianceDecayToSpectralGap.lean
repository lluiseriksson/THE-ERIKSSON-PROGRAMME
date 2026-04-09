/-
  C83: Bridge from pointwise exponential decay to HasSpectralGap.
  Core math: if ||(T^n - P0) x|| <= exp(-g*n)*||x|| for all x, n, then
  ||T^n - P0|| <= exp(-g*n) by opNorm_le_bound. Hence HasSpectralGap T P0 g 1.
  Oracle: [propext, Classical.choice, Quot.sound]. No sorry.
-/
import Mathlib.Analysis.NormedSpace.OperatorNorm.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import YangMills.L4_TransferMatrix.TransferMatrix

namespace YangMills

open Real ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- **C83-MAIN**: Pointwise exponential decay of (T^n - P₀) implies
    HasSpectralGap with constant 1. -/
theorem hasSpectralGap_of_pointwiseDecay
    (T P₀ : H →L[ℝ] H) (γ : ℝ) (hγ : 0 < γ)
    (h : ∀ n : ℕ, ∀ x : H, ‖(T ^ n - P₀) x‖ ≤ Real.exp (-γ * ↑n) * ‖x‖) :
    HasSpectralGap T P₀ γ 1 :=
  ⟨hγ, one_pos, fun n ↦ by
    rw [one_mul]
    exact opNorm_le_bound _ (Real.exp_nonneg _) (h n)⟩

/-- **C83-COR**: Variant with prefactor C > 0. -/
theorem hasSpectralGap_of_pointwiseDecay_const
    (T P₀ : H →L[ℝ] H) (γ C : ℝ) (hγ : 0 < γ) (hC : 0 < C)
    (h : ∀ n : ℕ, ∀ x : H, ‖(T ^ n - P₀) x‖ ≤ C * Real.exp (-γ * ↑n) * ‖x‖) :
    HasSpectralGap T P₀ γ C :=
  ⟨hγ, hC, fun n ↦ by
    apply opNorm_le_bound _ (mul_nonneg hC.le (Real.exp_nonneg _))
    intro x
    exact h n x⟩

end YangMills
