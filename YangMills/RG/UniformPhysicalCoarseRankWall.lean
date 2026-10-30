import YangMills.RG.PhysicalFourierRankObstruction

/-! Uniform unit-spacing flat coercivity is impossible with fixed-dimensional
    coarse data and uniformly bounded repair/sector rank. Physical L^2-scaled
    operators and interacting Hessians are not covered. -/
namespace YangMills.RG
open Module
open scoped BigOperators RealInnerProductSpace

theorem physicalBand_budget_exceeded {d : ℕ} [NeZero d] (M r : ℕ) :
    M + r < 2 * (2 * (M + r + 1) + 1) ^ d := by
  have hd := NeZero.pos d
  have hp : 2 * (M + r + 1) + 1 ≤ (2 * (M + r + 1) + 1) ^ d := by
    simpa only [pow_one] using
      (Nat.pow_le_pow_right (by omega : 1 ≤ 2 * (M + r + 1) + 1) (by omega : 1 ≤ d))
  omega

set_option maxHeartbeats 800000 in
theorem exists_refinement_below_threshold (d N' R : ℕ) [NeZero N']
    (c : ℝ) (hc : 0 < c) :
    ∃ L : ℕ, 2 * R < (L + 1) * N' ∧
      4 * Real.pi ^ 2 * (d : ℝ) * (R : ℝ) ^ 2 / (((L + 1) * N' : ℕ) : ℝ) ^ 2 < c := by
  let a : ℝ := 4 * Real.pi ^ 2 * (d : ℝ) * (R : ℝ) ^ 2
  obtain ⟨L, hL⟩ := exists_nat_gt (max (((2 * R : ℕ) : ℝ)) (max (a / c) 1))
  have hLR : ((2 * R : ℕ) : ℝ) < (L : ℝ) :=
    lt_of_le_of_lt (le_max_left _ _) hL
  have hLa : a / c < (L : ℝ) :=
    lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_right _ _)) hL
  have hL1 : (1 : ℝ) < (L : ℝ) :=
    lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_right _ _)) hL
  have hN : (1 : ℝ) ≤ (N' : ℝ) := by exact_mod_cast (NeZero.pos N')
  let n := (L + 1) * N'
  have hstep : (L : ℝ) + 1 ≤ (n : ℝ) := by
    dsimp [n]
    push_cast
    nlinarith [mul_nonneg (by positivity : 0 ≤ (L : ℝ) + 1) (sub_nonneg.mpr hN)]
  have hnL : (L : ℝ) < (n : ℝ) := by linarith
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by linarith
  have hnn : (n : ℝ) ≤ (n : ℝ) ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hn1) hn0.le]
  have hLs : (L : ℝ) ≤ (n : ℝ) ^ 2 := le_trans hnL.le hnn
  have ha : a < c * (L : ℝ) := by
    simpa [mul_comm] using (div_lt_iff₀ hc).mp hLa
  refine ⟨L, ?_, ?_⟩
  · exact_mod_cast (lt_trans hLR hnL)
  · change a / (n : ℝ) ^ 2 < c
    apply (div_lt_iff₀ (sq_pos_of_pos hn0)).mpr
    exact lt_of_lt_of_le ha (mul_le_mul_of_nonneg_left hLs hc.le)

section FiniteSector
variable {d n Nc : ℕ} [NeZero d] [NeZero n] [NeZero Nc]
variable {F : Type*} [AddCommGroup F] [Module ℝ F] [FiniteDimensional ℝ F]

set_option maxHeartbeats 1200000 in
theorem physical_band_restricted_estimate_false
    (hNc : 2 ≤ Nc) (ρ : SUNAdjointModel Nc) (j : Fin d) (R : ℕ) (hR : 2 * R < n)
    (C : PhysicalGaugeOneCochain d n Nc →ₗ[ℝ] F)
    (P : PhysicalGaugeOneCochain d n Nc →ₗ[ℝ] PhysicalGaugeOneCochain d n Nc)
    (Phi : F → ℝ) (hPhi : Phi 0 = 0) (c : ℝ)
    (hc : 4 * Real.pi ^ 2 * (d : ℝ) * (R : ℝ) ^ 2 / (n : ℝ) ^ 2 < c)
    (hdim : finrank ℝ F + finrank ℝ (LinearMap.range P) < 2 * (2 * R + 1) ^ d) :
    ¬ ∀ A : PhysicalGaugeOneCochain d n Nc, P A = 0 →
      c * ‖A‖ ^ 2 ≤ inner ℝ A (flatGaugeHodgeK0CLM d n Nc ρ A) + Phi (C A) := by
  intro hbound
  have hdim' : finrank ℝ F + finrank ℝ (LinearMap.range P) <
      finrank ℝ (physicalCenteredFourierBand (n := n) hNc j R) := by
    rw [physicalCenteredFourierBand_finrank hNc j R hR]
    exact hdim
  rcases exists_unseen_of_finrank_lt_measurement_add_repair
      (physicalCenteredFourierBand hNc j R) C P hdim' with ⟨A, hAS, hA, hCA, hPA⟩
  have hlo : c * ‖A‖ ^ 2 ≤ inner ℝ A (flatGaugeHodgeK0CLM d n Nc ρ A) := by
    simpa [hCA, hPhi] using hbound A hPA
  have hhi := physicalCenteredFourierBand_hodge_le hNc ρ j R hR A hAS
  have hpos : 0 < ‖A‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hA)
  have hs := mul_lt_mul_of_pos_right hc hpos
  linarith
end FiniteSector

local instance refinementSide_neZero (L N' : ℕ) [NeZero N'] : NeZero ((L + 1) * N') :=
  ⟨Nat.mul_ne_zero (Nat.succ_ne_zero L) (NeZero.ne N')⟩

abbrev RefinedPhysicalOneCochain (d N' Nc L : ℕ) [NeZero N'] :=
  PhysicalGaugeOneCochain d ((L + 1) * N') Nc

section Uniform
variable {d Nc N' : ℕ} [NeZero d] [NeZero Nc] [NeZero N']
variable {F : Type*} [AddCommGroup F] [Module ℝ F] [FiniteDimensional ℝ F]

set_option maxHeartbeats 1600000 in
theorem no_uniform_coarse_finite_rank_repair
    (hNc : 2 ≤ Nc) (ρ : SUNAdjointModel Nc) (j : Fin d)
    (C : ∀ L, RefinedPhysicalOneCochain d N' Nc L →ₗ[ℝ] F)
    (V : ∀ L, RefinedPhysicalOneCochain d N' Nc L →ₗ[ℝ] RefinedPhysicalOneCochain d N' Nc L)
    (Phi : ℕ → F → ℝ) (hPhi : ∀ L, Phi L 0 = 0)
    (r : ℕ) (hrank : ∀ L, finrank ℝ (LinearMap.range (V L)) ≤ r) :
    ¬ ∃ c : ℝ, 0 < c ∧ ∀ L (A : RefinedPhysicalOneCochain d N' Nc L),
      c * ‖A‖ ^ 2 ≤ inner ℝ A (flatGaugeHodgeK0CLM d ((L + 1) * N') Nc ρ A) +
        Phi L (C L A) + inner ℝ A (V L A) := by
  rintro ⟨c, hc, hbound⟩
  let R := finrank ℝ F + r + 1
  obtain ⟨L, hR, hb⟩ := exists_refinement_below_threshold d N' R c hc
  have hdim : finrank ℝ F + r < 2 * (2 * R + 1) ^ d :=
    physicalBand_budget_exceeded (d := d) (finrank ℝ F) r
  have hbudget := physicalCenteredFourierBand_coercivity_budget
    hNc ρ j R hR (C L) (V L) (Phi L) (hPhi L) c hb (hbound L)
  have hle : 2 * (2 * R + 1) ^ d ≤ finrank ℝ F + r :=
    le_trans hbudget (Nat.add_le_add_left (hrank L) (finrank ℝ F))
  exact (not_le_of_gt hdim) hle

set_option maxHeartbeats 1600000 in
theorem no_uniform_coarse_finite_rank_sector
    (hNc : 2 ≤ Nc) (ρ : SUNAdjointModel Nc) (j : Fin d)
    (C : ∀ L, RefinedPhysicalOneCochain d N' Nc L →ₗ[ℝ] F)
    (P : ∀ L, RefinedPhysicalOneCochain d N' Nc L →ₗ[ℝ] RefinedPhysicalOneCochain d N' Nc L)
    (Phi : ℕ → F → ℝ) (hPhi : ∀ L, Phi L 0 = 0)
    (r : ℕ) (hrank : ∀ L, finrank ℝ (LinearMap.range (P L)) ≤ r) :
    ¬ ∃ c : ℝ, 0 < c ∧ ∀ L (A : RefinedPhysicalOneCochain d N' Nc L), P L A = 0 →
      c * ‖A‖ ^ 2 ≤ inner ℝ A (flatGaugeHodgeK0CLM d ((L + 1) * N') Nc ρ A) +
        Phi L (C L A) := by
  rintro ⟨c, hc, hbound⟩
  let R := finrank ℝ F + r + 1
  obtain ⟨L, hR, hb⟩ := exists_refinement_below_threshold d N' R c hc
  have hdim : finrank ℝ F + r < 2 * (2 * R + 1) ^ d :=
    physicalBand_budget_exceeded (d := d) (finrank ℝ F) r
  have hdim' : finrank ℝ F + finrank ℝ (LinearMap.range (P L)) < 2 * (2 * R + 1) ^ d :=
    lt_of_le_of_lt (Nat.add_le_add_left (hrank L) (finrank ℝ F)) hdim
  exact physical_band_restricted_estimate_false hNc ρ j R hR
    (C L) (P L) (Phi L) (hPhi L) c hb hdim' (hbound L)
end Uniform
end YangMills.RG
