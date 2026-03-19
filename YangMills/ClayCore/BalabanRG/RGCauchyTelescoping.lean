import Mathlib
import YangMills.ClayCore.BalabanRG.ActivitySpaceNorms

namespace YangMills.ClayCore

open scoped BigOperators
open Classical

/-! # RGCauchyTelescoping — Layer 11G. No physics. No sorrys. -/

noncomputable section

variable {d : ℕ} {k : ℕ} [ActivityNorm d k]

/-- Lipschitz iterate bound: ‖fⁿ K₁ - fⁿ K₂‖ ≤ ρⁿ ‖K₁ - K₂‖. -/
theorem lipschitz_iterate_bound
    (f : ActivityFamily d k → ActivityFamily d k)
    (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hf : ∀ K₁ K₂, ActivityNorm.dist (f K₁) (f K₂) ≤ ρ * ActivityNorm.dist K₁ K₂)
    (n : ℕ) (K₁ K₂ : ActivityFamily d k) :
    ActivityNorm.dist (f^[n] K₁) (f^[n] K₂) ≤ ρ^n * ActivityNorm.dist K₁ K₂ := by
  induction n generalizing K₁ K₂ with
  | zero => simp
  | succ n ih =>
      -- f^[n+1] K = f (f^[n] K)  OR  f^[n] (f K) depending on Mathlib version
      -- Use show to fix the goal form, then apply le_trans chain
      show ActivityNorm.dist (f^[n+1] K₁) (f^[n+1] K₂) ≤ ρ^(n+1) * ActivityNorm.dist K₁ K₂
      have hiter : f^[n+1] K₁ = f^[n] (f K₁) ∧ f^[n+1] K₂ = f^[n] (f K₂) := by
        simp [Function.iterate_succ_apply]
      rw [hiter.1, hiter.2]
      have hpow : 0 ≤ ρ^n := pow_nonneg hρ n
      have step1 : ActivityNorm.dist (f^[n] (f K₁)) (f^[n] (f K₂))
          ≤ ρ^n * ActivityNorm.dist (f K₁) (f K₂) := ih (f K₁) (f K₂)
      have step2 : ρ^n * ActivityNorm.dist (f K₁) (f K₂)
          ≤ ρ^n * (ρ * ActivityNorm.dist K₁ K₂) :=
        mul_le_mul_of_nonneg_left (hf K₁ K₂) hpow
      have step3 : ρ^n * (ρ * ActivityNorm.dist K₁ K₂)
          = ρ^(n+1) * ActivityNorm.dist K₁ K₂ := by rw [pow_succ]; ring
      linarith

theorem contraction_geometric_decay
    (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (n : ℕ) : ρ^n ≤ 1 :=
  pow_le_one₀ hρ0 hρ1.le

theorem scale_uniform_contraction
    {k' : ℕ} [ActivityNorm d k']
    (T : ActivityFamily d k → ActivityFamily d k')
    (ρ : ℝ)
    (hT : ∀ K₁ K₂, ActivityNorm.dist (T K₁) (T K₂) ≤ ρ * ActivityNorm.dist K₁ K₂)
    (K₁ K₂ : ActivityFamily d k) :
    ActivityNorm.dist (T K₁) (T K₂) ≤ ρ * ActivityNorm.dist K₁ K₂ :=
  hT K₁ K₂

end

end YangMills.ClayCore
