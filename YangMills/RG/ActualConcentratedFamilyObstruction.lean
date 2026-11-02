import YangMills.RG.ActualConcentratedVolumeRank

/-! Explicit bounded-rank tail obstruction. The threshold depends on d, Nc,
c and the rank budget, not on the repair mean or local neighbourhood data. -/
namespace YangMills.RG
open Module
open scoped BigOperators RealInnerProductSpace
set_option maxHeartbeats 1800000

theorem actualConcentrated_volume_dominates_side (d n : ℕ) (hn : 1 ≤ n) :
    n ≤ n^(d + 2) := by
  calc
    n = n^1 := (pow_one n).symm
    _ ≤ n^(d + 2) := pow_le_pow_right₀ hn (by omega)

section Finite
variable {d n Nc : ℕ} [NeZero n] [NeZero Nc]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

theorem actualConcentrated_bounded_rank_obstruction
    (hNc : 2 ≤ Nc) (rho : SUNAdjointModel Nc) (k : ℕ) (hk : 3 ≤ k) (hn : k ≤ n)
    (q : ℕ) (hdim : finrank ℝ F ≤ q)
    (htail : k^(d + 2) * (q + (d + 2)^2 * (Nc^2 - 1)) < n)
    (x0 : FinBox (d + 2) n) (b : ℝ)
    (C : PhysicalGaugeOneCochain (d + 2) n Nc → F)
    (L : PhysicalGaugeOneCochain (d + 2) n Nc →L[ℝ] F)
    (hC : HasFDerivAt C L 0) (hC0 : C 0 = 0)
    (Phi : F → ℝ) (K delta radius c : ℝ) (hc : 0 < c)
    (hdelta : 0 < delta) (hradius : 0 < radius)
    (hPhi : ∀ y, ‖y‖ < delta → Phi y ≤ K * ‖y‖^2)
    (hscale : 4 * Real.pi^2 * ((d + 2 : ℕ) : ℝ) / (k : ℝ)^2 ≤ c / 2) :
    ¬ ∀ A : PhysicalGaugeOneCochain (d + 2) n Nc,
      gaugeConstraintQCLM rho (trivialPhysicalGaugeBackground (d + 2) n Nc) A = 0 →
      ‖A‖ < radius → c * ‖A‖^2 ≤
        inner ℝ A (flatGaugeHodgeK0CLM (d + 2) n Nc rho A) +
        inner ℝ A (componentwiseWeightedRepairCLM (actualConcentratedWeight x0 b) A) +
        Phi (C A) := by
  intro hlocal
  have hr := actualConcentrated_quotient_rank hNc rho k hk hn x0 C L hC hC0
    Phi K delta radius c hc hdelta hradius hPhi hscale b hlocal
  have hbudget := Nat.mul_le_mul_left (k^(d + 2))
    (Nat.add_le_add_right hdim ((d + 2)^2 * (Nc^2 - 1)))
  have hside := actualConcentrated_volume_dominates_side d n (by omega)
  exact (not_lt_of_ge (hside.trans (hr.trans hbudget))) htail
end Finite

theorem actualConcentrated_uniform_bounded_rank_tail {d Nc : ℕ} [NeZero Nc]
    (hNc : 2 ≤ Nc) (rho : SUNAdjointModel Nc) (c : ℝ) (hc : 0 < c) (q : ℕ) :
    ∃ N : ℕ, 1 ≤ N ∧
      ∀ (n : ℕ) [NeZero n] (hn : N ≤ n)
        (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
        (hdim : finrank ℝ F ≤ q) (x0 : FinBox (d + 2) n) (m : ℝ) (hm : 1 ≤ m)
        (C : PhysicalGaugeOneCochain (d + 2) n Nc → F)
        (L : PhysicalGaugeOneCochain (d + 2) n Nc →L[ℝ] F)
        (hC : HasFDerivAt C L 0) (hC0 : C 0 = 0) (Phi : F → ℝ)
        (K delta radius : ℝ) (hdelta : 0 < delta) (hradius : 0 < radius)
        (hPhi : ∀ y, ‖y‖ < delta → Phi y ≤ K * ‖y‖^2),
        ¬ ∀ A : PhysicalGaugeOneCochain (d + 2) n Nc,
          gaugeConstraintQCLM rho (trivialPhysicalGaugeBackground (d + 2) n Nc) A = 0 →
          ‖A‖ < radius → c * ‖A‖^2 ≤
            inner ℝ A (flatGaugeHodgeK0CLM (d + 2) n Nc rho A) +
            inner ℝ A (componentwiseWeightedRepairCLM
              (actualConcentratedWeight x0 ((m - 1) * (n : ℝ)^(d + 2))) A) + Phi (C A) := by
  obtain ⟨k, hk, hs⟩ := actualConcentrated_cutoff_exists d c hc
  refine ⟨max k (k^(d + 2) * (q + (d + 2)^2 * (Nc^2 - 1)) + 1), by omega, ?_⟩
  intro n _ hn F _ _ _ hdim x0 m _ C L hC hC0 Phi K delta radius hdelta hradius hPhi
  have hkn : k ≤ n := le_trans (le_max_left _ _) hn
  have htail : k^(d + 2) * (q + (d + 2)^2 * (Nc^2 - 1)) < n := by
    have hh := le_trans (le_max_right k
      (k^(d + 2) * (q + (d + 2)^2 * (Nc^2 - 1)) + 1)) hn
    omega
  exact actualConcentrated_bounded_rank_obstruction hNc rho k hk hkn q hdim htail x0
    ((m - 1) * (n : ℝ)^(d + 2)) C L hC hC0 Phi K delta radius c hc hdelta hradius hPhi hs
end YangMills.RG
