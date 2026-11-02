import YangMills.RG.ActualConcentratedCoexactRank
import YangMills.RG.ActualVolumeFullTailDensity

/-! Derived quotient cutoff and actual nonnegative-profile finite-tail rank.
Original local nonlinear data are retained; no uniform neighbourhood assumption. -/
namespace YangMills.RG
open Module
open scoped BigOperators RealInnerProductSpace
set_option maxHeartbeats 1800000

theorem actualConcentrated_cutoff_exists (d : ℕ) (c : ℝ) (hc : 0 < c) :
    ∃ k : ℕ, 3 ≤ k ∧ 4 * Real.pi^2 * ((d + 2 : ℕ) : ℝ) / (k : ℝ)^2 ≤ c / 2 := by
  obtain ⟨s, hs⟩ := coexact_dilation_scale_exists d 0 (c / 2) (by linarith)
  refine ⟨s + 3, by omega, le_of_lt ?_⟩
  simpa only [add_zero, one_mul] using hs

theorem actualConcentrated_quotient_gap (d k n : ℕ) (c : ℝ) (hc : 0 < c)
    (hk : 3 ≤ k) (hn : k ≤ n)
    (hscale : 4 * Real.pi^2 * ((d + 2 : ℕ) : ℝ) / (k : ℝ)^2 ≤ c / 2) :
    4 * Real.pi^2 * ((d + 2 : ℕ) : ℝ) * ((n / k : ℕ) : ℝ)^2 / (n : ℝ)^2 < c := by
  have hb := actualVolume_quotient_spectral_bound d k n hk hn
  exact lt_of_le_of_lt (hb.trans hscale) (by linarith)

theorem actualConcentrated_quotient_volume_nat (d k n : ℕ) (hk : 3 ≤ k) (hn : k ≤ n) :
    n^(d + 2) ≤ k^(d + 2) * (2 * (n / k) * (2 * (n / k) + 1)^(d + 1)) := by
  have h := actualVolume_quotient_volume_bound d k n hk hn
  exact_mod_cast h

section Original
variable {d n Nc : ℕ} [NeZero n] [NeZero Nc]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
variable (hNc : 2 ≤ Nc) (rho : SUNAdjointModel Nc) (k : ℕ) (hk : 3 ≤ k) (hn : k ≤ n)
variable (x0 : FinBox (d + 2) n)
variable (C : PhysicalGaugeOneCochain (d + 2) n Nc → F)
variable (L : PhysicalGaugeOneCochain (d + 2) n Nc →L[ℝ] F)
variable (hC : HasFDerivAt C L 0) (hC0 : C 0 = 0)
variable (Phi : F → ℝ) (K delta radius c : ℝ) (hc : 0 < c)
variable (hdelta : 0 < delta) (hradius : 0 < radius)
variable (hPhi : ∀ y, ‖y‖ < delta → Phi y ≤ K * ‖y‖^2)
variable (hscale : 4 * Real.pi^2 * ((d + 2 : ℕ) : ℝ) / (k : ℝ)^2 ≤ c / 2)

include hNc rho k hk hn x0 C L hC hC0 Phi K delta radius c hc hdelta hradius hPhi hscale

theorem actualConcentrated_quotient_rank (b : ℝ)
    (hlocal : ∀ A : PhysicalGaugeOneCochain (d + 2) n Nc,
      gaugeConstraintQCLM rho (trivialPhysicalGaugeBackground (d + 2) n Nc) A = 0 →
      ‖A‖ < radius → c * ‖A‖^2 ≤
        inner ℝ A (flatGaugeHodgeK0CLM (d + 2) n Nc rho A) +
        inner ℝ A (componentwiseWeightedRepairCLM (actualConcentratedWeight x0 b) A) + Phi (C A)) :
    n^(d + 2) ≤ k^(d + 2) * (finrank ℝ F + (d + 2)^2 * (Nc^2 - 1)) := by
  have hR := (actualVolume_quotient_cutoff k n hk hn).2.1
  have hgap := actualConcentrated_quotient_gap d k n c hc hk hn hscale
  have hrank := actualConcentrated_coexact_rank hNc rho (n / k) hR x0 b C L hC hC0
    Phi K delta radius c hdelta hradius hPhi hgap hlocal
  exact (actualConcentrated_quotient_volume_nat d k n hk hn).trans
    (Nat.mul_le_mul_left (k^(d + 2)) hrank)

theorem actualConcentrated_nonnegative_profile_rank (m : ℝ) (hm : 1 ≤ m)
    (hlocal : ∀ A : PhysicalGaugeOneCochain (d + 2) n Nc,
      gaugeConstraintQCLM rho (trivialPhysicalGaugeBackground (d + 2) n Nc) A = 0 →
      ‖A‖ < radius → c * ‖A‖^2 ≤
        inner ℝ A (flatGaugeHodgeK0CLM (d + 2) n Nc rho A) +
        inner ℝ A (componentwiseWeightedRepairCLM
          (actualConcentratedWeight x0 ((m - 1) * (n : ℝ)^(d + 2))) A) + Phi (C A)) :
    (∀ p, 0 ≤ actualConcentratedWeight x0 ((m - 1) * (n : ℝ)^(d + 2)) p) ∧
    (∀ i j : Fin (d + 2),
      (∑ x : FinBox (d + 2) n,
        max (1 + actualConcentratedWeight x0 ((m - 1) * (n : ℝ)^(d + 2)) (i, (x, j))) 0) =
        (n : ℝ)^(d + 2) * m) ∧
    n^(d + 2) ≤ k^(d + 2) * (finrank ℝ F + (d + 2)^2 * (Nc^2 - 1)) := by
  refine ⟨actualConcentrated_weight_nonneg x0 _ (mul_nonneg (sub_nonneg.mpr hm)
    (by positivity)), ?_, ?_⟩
  · intro i j
    exact actualConcentrated_positive_total_budget x0 m hm i j
  · exact actualConcentrated_quotient_rank hNc rho k hk hn x0 C L hC hC0 Phi K delta radius c
      hc hdelta hradius hPhi hscale ((m - 1) * (n : ℝ)^(d + 2)) hlocal
end Original
end YangMills.RG
