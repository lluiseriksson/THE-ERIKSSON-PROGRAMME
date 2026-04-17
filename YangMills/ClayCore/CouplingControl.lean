import Mathlib

/-!
# Coupling Control (Proposition 4.1 of [Eriksson Feb 2026])

If `g₀ ≤ γ₀` with γ₀ small enough that C·γ₀² < b₀/2,
with b₀ = 11·N_c/(48·π²) the one-loop β-function coefficient
and C the remainder-bound constant in the recursion
1/g_{k+1}² = 1/g_k² + b₀ + r_k, |r_k| ≤ C · g_k²,
then g_k ≤ γ₀ for every k ≤ k_star.
-/

namespace YangMills

noncomputable section

open Real

/-- One-loop β-function coefficient b₀ = 11·N_c/(48·π²). -/
noncomputable def betaOneLoop (N_c : ℕ) : ℝ :=
  11 * (N_c : ℝ) / (48 * Real.pi ^ 2)

theorem betaOneLoop_pos (N_c : ℕ) [NeZero N_c] : 0 < betaOneLoop N_c := by
  unfold betaOneLoop
  have hN : (0 : ℝ) < (N_c : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N_c)
  positivity

/-- Hypotheses for Proposition 4.1: a coupling sequence satisfying the
one-loop β recursion with signed remainder bounded by `C · g_k²`. -/
structure CouplingRecursionHyp (N_c : ℕ) (k_star : ℕ) where
  g : ℕ → ℝ
  hg_pos : ∀ k ≤ k_star, 0 < g k
  C_rem : ℝ
  hC_pos : 0 < C_rem
  h_remainder : ∀ k < k_star,
    |1 / g (k+1) ^ 2 - 1 / g k ^ 2 - betaOneLoop N_c| ≤ C_rem * g k ^ 2

/-- **Proposition 4.1 (coupling control).**
If `g 0 ≤ γ₀` and `γ₀ > 0` is small enough that
`C · γ₀² < b₀/2`, then `g k ≤ γ₀` for every `k ≤ k_star`. -/
theorem coupling_control {N_c : ℕ} [NeZero N_c] {k_star : ℕ}
    (H : CouplingRecursionHyp N_c k_star)
    {γ₀ : ℝ} (hγ_pos : 0 < γ₀)
    (hγ_small : H.C_rem * γ₀ ^ 2 < betaOneLoop N_c / 2)
    (hg0 : H.g 0 ≤ γ₀) :
    ∀ k ≤ k_star, H.g k ≤ γ₀ := by
  intro k
  induction k with
  | zero => intro _; exact hg0
  | succ n ih =>
    intro hk_succ
    have hn_le : n ≤ k_star := Nat.le_of_succ_le hk_succ
    have hn_lt : n < k_star := hk_succ
    have hg_n_le : H.g n ≤ γ₀ := ih hn_le
    have hgn_pos : 0 < H.g n := H.hg_pos n hn_le
    have hgn_succ_pos : 0 < H.g (n+1) := H.hg_pos (n+1) hk_succ
    have hb0_pos : 0 < betaOneLoop N_c := betaOneLoop_pos N_c
    have hgn_sq_pos : 0 < H.g n ^ 2 := by positivity
    have hgn_succ_sq_pos : 0 < H.g (n+1) ^ 2 := by positivity
    -- g_n² ≤ γ₀²
    have hgn_sq_le : H.g n ^ 2 ≤ γ₀ ^ 2 := by
      have h := mul_self_le_mul_self hgn_pos.le hg_n_le
      nlinarith [h]
    -- |r_n| ≤ C · γ₀² < b₀/2
    have h_rem : |1 / H.g (n+1) ^ 2 - 1 / H.g n ^ 2 - betaOneLoop N_c|
        ≤ H.C_rem * H.g n ^ 2 := H.h_remainder n hn_lt
    have h_rem_bound : H.C_rem * H.g n ^ 2 ≤ H.C_rem * γ₀ ^ 2 :=
      mul_le_mul_of_nonneg_left hgn_sq_le H.hC_pos.le
    have h_rem_small : |1 / H.g (n+1) ^ 2 - 1 / H.g n ^ 2 - betaOneLoop N_c|
        < betaOneLoop N_c / 2 :=
      lt_of_le_of_lt (le_trans h_rem h_rem_bound) hγ_small
    -- 1/g_{n+1}² > 1/g_n² + b₀/2 > 1/g_n²
    have h_abs := abs_lt.mp h_rem_small
    have h_diff : 1 / H.g (n+1) ^ 2 - 1 / H.g n ^ 2 > betaOneLoop N_c / 2 := by
      linarith [h_abs.1]
    have h_inv_lt : 1 / H.g n ^ 2 < 1 / H.g (n+1) ^ 2 := by linarith
    -- g_{n+1}² < g_n² (via contrapositive of monotone 1/x)
    have h_sq_lt : H.g (n+1) ^ 2 < H.g n ^ 2 := by
      by_contra hge
      push_neg at hge
      have : 1 / H.g (n+1) ^ 2 ≤ 1 / H.g n ^ 2 :=
        one_div_le_one_div_of_le hgn_sq_pos hge
      linarith
    -- g_{n+1}² < γ₀²
    have h_sq_lt_γ : H.g (n+1) ^ 2 < γ₀ ^ 2 :=
      lt_of_lt_of_le h_sq_lt hgn_sq_le
    -- Conclude g_{n+1} ≤ γ₀
    by_contra hne
    push_neg at hne
    have h_sq_ge : γ₀ ^ 2 ≤ H.g (n+1) ^ 2 := by
      have h := mul_self_le_mul_self hγ_pos.le hne.le
      nlinarith [h]
    linarith

end

end YangMills
