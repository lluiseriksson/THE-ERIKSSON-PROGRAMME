import YangMills.RG.ActualVolumeNumericalDensity

/-! Full integer-tail mean-budget density. Natural quotient estimates,
actual spectral cutoff and volume comparison are derived. All original local
nonlinear data remain explicit at each n; no uniform penalty neighbourhood. -/
namespace YangMills.RG
open Module
open scoped BigOperators RealInnerProductSpace
set_option maxHeartbeats 1800000

theorem actualVolume_quotient_cutoff (k n : ℕ) (hk : 3 ≤ k) (hn : k ≤ n) :
    0 < n / k ∧ 2 * (n / k) < n ∧ k * (n / k) ≤ n ∧ n ≤ k * (2 * (n / k)) := by
  have hk0 : 0 < k := by omega
  have hpos : 0 < n / k := Nat.div_pos hn hk0
  have hlo : k * (n / k) ≤ n := by
    simpa only [Nat.mul_comm] using (Nat.div_mul_le_self n k)
  have hup : n < k * (n / k + 1) := by
    have hmod := Nat.mod_lt n hk0
    have hid := Nat.mod_add_div n k
    nlinarith
  refine ⟨hpos, ?_, hlo, ?_⟩
  · exact lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_right (by omega : 2 < k) hpos) hlo
  · calc
      n ≤ k * (n / k + 1) := Nat.le_of_lt hup
      _ ≤ k * (2 * (n / k)) := Nat.mul_le_mul_left k (by omega)

theorem actualVolume_quotient_spectral_bound (d k n : ℕ) (hk : 3 ≤ k) (hn : k ≤ n) :
    4 * Real.pi^2 * ((d + 2 : ℕ) : ℝ) * ((n / k : ℕ) : ℝ)^2 / (n : ℝ)^2 ≤
      4 * Real.pi^2 * ((d + 2 : ℕ) : ℝ) / (k : ℝ)^2 := by
  have hq := (actualVolume_quotient_cutoff k n hk hn).2.2.1
  have hprod : (k : ℝ) * ((n / k : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hq
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hsq : ((k : ℝ) * ((n / k : ℕ) : ℝ))^2 ≤ (n : ℝ)^2 := by
    have hp := mul_nonneg (sub_nonneg.mpr hprod)
      (show 0 ≤ (n : ℝ) + (k : ℝ) * ((n / k : ℕ) : ℝ) by positivity)
    nlinarith
  apply (div_le_div_iff₀ (sq_pos_of_pos hn0) (sq_pos_of_pos hk0)).2
  have hm := mul_le_mul_of_nonneg_left hsq
    (show 0 ≤ 4 * Real.pi^2 * ((d + 2 : ℕ) : ℝ) by positivity)
  nlinarith only [hm]

theorem actualVolume_quotient_volume_bound (d k n : ℕ) (hk : 3 ≤ k) (hn : k ≤ n) :
    (n : ℝ)^(d + 2) ≤ (k : ℝ)^(d + 2) *
      ((2 * (n / k) * (2 * (n / k) + 1)^(d + 1) : ℕ) : ℝ) := by
  have hq := (actualVolume_quotient_cutoff k n hk hn).2.2.2
  have hreal : (n : ℝ) ≤ (k : ℝ) * (2 * ((n / k : ℕ) : ℝ)) := by exact_mod_cast hq
  have hp : (n : ℝ)^(d + 2) ≤ ((k : ℝ) * (2 * ((n / k : ℕ) : ℝ)))^(d + 2) := by
    gcongr <;> assumption
  have hb : (2 * ((n / k : ℕ) : ℝ))^(d + 2) ≤
      ((2 * (n / k) * (2 * (n / k) + 1)^(d + 1) : ℕ) : ℝ) := by
    exact_mod_cast coexact_band_power_bound d (n / k)
  calc
    _ ≤ ((k : ℝ) * (2 * ((n / k : ℕ) : ℝ)))^(d + 2) := hp
    _ = (k : ℝ)^(d + 2) * (2 * ((n / k : ℕ) : ℝ))^(d + 2) := mul_pow _ _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left hb (by positivity)

section FiniteTail
variable {d n Nc : ℕ} [NeZero n] [NeZero Nc]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

theorem actualVolumeMean_full_tail_density (hNc : 2 ≤ Nc) (rho : SUNAdjointModel Nc)
    (k : ℕ) (hk : 3 ≤ k) (hn : k ≤ n) (m : ℝ) (hm : 0 ≤ m) (c : ℝ) (hc : 0 < c)
    (hscale : 2 * m * 4 * Real.pi^2 * ((d + 2 : ℕ) : ℝ) / (k : ℝ)^2 ≤ c)
    (w : PhysicalGradientIndex (d + 2) n → ℝ)
    (hw : ∀ i l, l = 0 ∨ l = Fin.succ 0 →
      ∑ x : FinBox (d + 2) n, max (1 + w (i, (x, l))) 0 ≤ (n : ℝ)^(d + 2) * m)
    (C : PhysicalGaugeOneCochain (d + 2) n Nc → F)
    (L : PhysicalGaugeOneCochain (d + 2) n Nc →L[ℝ] F)
    (hC : HasFDerivAt C L 0) (hC0 : C 0 = 0)
    (Phi : F → ℝ) (K delta radius : ℝ) (hdelta : 0 < delta) (hradius : 0 < radius)
    (hPhi : ∀ y, ‖y‖ < delta → Phi y ≤ K * ‖y‖^2)
    (hlocal : ∀ A : PhysicalGaugeOneCochain (d + 2) n Nc,
      gaugeConstraintQCLM rho (trivialPhysicalGaugeBackground (d + 2) n Nc) A = 0 →
      ‖A‖ < radius → c * ‖A‖^2 ≤
        inner ℝ A (flatGaugeHodgeK0CLM (d + 2) n Nc rho A) +
        inner ℝ A (componentwiseWeightedRepairCLM w A) + Phi (C A)) :
    (1 / (2 * (k : ℝ)^(d + 2))) * (n : ℝ)^(d + 2) ≤ (finrank ℝ F : ℝ) := by
  have hcut := (actualVolume_quotient_cutoff k n hk hn).2.1
  have hr := actualVolumeMean_numerical_rank hNc rho (n / k) hcut w m hm hw
    C L hC hC0 Phi K delta radius c (le_of_lt hc) hdelta hradius hPhi hlocal
  let H : ℝ := ((2 * (n / k) * (2 * (n / k) + 1)^(d + 1) : ℕ) : ℝ)
  let B : ℝ := 4 * Real.pi^2 * ((d + 2 : ℕ) : ℝ) / (k : ℝ)^2
  have hbeta := actualVolume_quotient_spectral_bound d k n hk hn
  have ht := mul_le_mul_of_nonneg_left hbeta (show 0 ≤ m * H by positivity)
  have hr' : c * (H - (finrank ℝ F : ℝ)) ≤ m * H * B := hr.trans ht
  have hs : 2 * m * B ≤ c := by
    dsimp [B]
    convert hscale using 1 <;> ring
  have hsH := mul_le_mul_of_nonneg_right hs (show 0 ≤ H by positivity)
  have hhalf : H ≤ 2 * (finrank ℝ F : ℝ) := by
    by_contra hh
    have hp : 0 < c * (H - 2 * (finrank ℝ F : ℝ)) := mul_pos hc (by linarith)
    nlinarith [hsH]
  have hv := actualVolume_quotient_volume_bound d k n hk hn
  change (n : ℝ)^(d + 2) ≤ (k : ℝ)^(d + 2) * H at hv
  have hdim := mul_le_mul_of_nonneg_left hhalf
    (show 0 ≤ (k : ℝ)^(d + 2) by positivity)
  have hden : 0 < 2 * (k : ℝ)^(d + 2) := by
    have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
    positivity
  have heq : (1 / (2 * (k : ℝ)^(d + 2))) * (n : ℝ)^(d + 2) =
      (n : ℝ)^(d + 2) / (2 * (k : ℝ)^(d + 2)) := by ring
  rw [heq]
  apply (div_le_iff₀ hden).2
  nlinarith [hv, hdim]
end FiniteTail

theorem actualVolumeMean_uniform_full_tail_density_exists {d Nc : ℕ} [NeZero Nc]
    (hNc : 2 ≤ Nc) (rho : SUNAdjointModel Nc) (m : ℝ) (hm : 0 ≤ m)
    (c : ℝ) (hc : 0 < c) :
    ∃ k : ℕ, 3 ≤ k ∧ ∃ epsilon : ℝ, 0 < epsilon ∧
      ∀ (n : ℕ) [NeZero n] (hn : k ≤ n)
        (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
        (w : PhysicalGradientIndex (d + 2) n → ℝ)
        (hw : ∀ i l, l = 0 ∨ l = Fin.succ 0 →
          ∑ x : FinBox (d + 2) n, max (1 + w (i, (x, l))) 0 ≤ (n : ℝ)^(d + 2) * m)
        (C : PhysicalGaugeOneCochain (d + 2) n Nc → F)
        (L : PhysicalGaugeOneCochain (d + 2) n Nc →L[ℝ] F)
        (hC : HasFDerivAt C L 0) (hC0 : C 0 = 0) (Phi : F → ℝ)
        (K delta radius : ℝ) (hdelta : 0 < delta) (hradius : 0 < radius)
        (hPhi : ∀ y, ‖y‖ < delta → Phi y ≤ K * ‖y‖^2)
        (hlocal : ∀ A : PhysicalGaugeOneCochain (d + 2) n Nc,
          gaugeConstraintQCLM rho (trivialPhysicalGaugeBackground (d + 2) n Nc) A = 0 →
          ‖A‖ < radius → c * ‖A‖^2 ≤
            inner ℝ A (flatGaugeHodgeK0CLM (d + 2) n Nc rho A) +
            inner ℝ A (componentwiseWeightedRepairCLM w A) + Phi (C A)),
        epsilon * (n : ℝ)^(d + 2) ≤ (finrank ℝ F : ℝ) := by
  obtain ⟨s, hs⟩ := coexact_dilation_scale_exists d (2 * m - 1) c hc
  have hscale : 2 * m * 4 * Real.pi^2 * ((d + 2 : ℕ) : ℝ) / ((s + 3 : ℕ) : ℝ)^2 ≤ c := by
    have hs' : 2 * m * 4 * Real.pi^2 * ((d + 2 : ℕ) : ℝ) /
        ((s + 3 : ℕ) : ℝ)^2 < c := by
      simpa only [show (1 : ℝ) + (2 * m - 1) = 2 * m by ring] using hs
    exact le_of_lt hs'
  refine ⟨s + 3, by omega, 1 / (2 * ((s + 3 : ℕ) : ℝ)^(d + 2)), by positivity, ?_⟩
  intro n _ hn F _ _ _ w hw C L hC hC0 Phi K delta radius hdelta hradius hPhi hlocal
  exact actualVolumeMean_full_tail_density hNc rho (s + 3) (by omega) hn m hm c hc hscale
    w hw C L hC hC0 Phi K delta radius hdelta hradius hPhi hlocal
end YangMills.RG
