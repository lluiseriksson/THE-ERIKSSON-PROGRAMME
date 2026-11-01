import YangMills.RG.ActualVolumeMeanRank
import YangMills.RG.TorusFourierEnergyBound
import YangMills.RG.CoexactUniformDensity

/-! Numerical finite rank and uniform dilation density for the actual packet.
Original signed weights have no lower bound; positive TOTAL occupied means
and original local nonlinear hypotheses remain explicit. No supplied spectral
certificate. The sharper exact-average/full-integer-tail limits are separate. -/
namespace YangMills.RG
open Module
open scoped BigOperators RealInnerProductSpace
set_option maxHeartbeats 1800000
variable {d n Nc : ℕ} [NeZero n] [NeZero Nc]

theorem positiveCoexact_multiplier_sum_sq_le (R : ℕ) (k : CoexactPositiveIndex d R) :
    (∑ i : Fin (d + 2), ‖positiveCoexactCharacter (n := n) R k
      (Pi.single i (1 : ZMod n)) - 1‖ ^ 2) ≤
      4 * Real.pi ^ 2 * ((d + 2 : ℕ) : ℝ) * (R : ℝ)^2 / (n : ℝ)^2 := by
  have h := centeredFourier_multiplier_sum_sq_le (n := n) R
    (coexactPositiveFourierIndex R k)
  have heq : ((d + 2 : ℕ) : ℝ) * (2 * Real.pi * (R : ℝ) / (n : ℝ))^2 =
      4 * Real.pi^2 * ((d + 2 : ℕ) : ℝ) * (R : ℝ)^2 / (n : ℝ)^2 := by
    rw [div_pow]
    ring
  rw [heq] at h
  simpa only [positiveCoexactCharacter, centeredFourierProfile] using h

theorem actualPacket_multiplier_trace_le (R : ℕ) :
    (∑ p : CoexactPositiveIndex d R × Bool, ∑ i : Fin (d + 2),
      ‖positiveCoexactCharacter (n := n) R p.1 (Pi.single i (1 : ZMod n)) - 1‖^2) ≤
    ((2 * R * (2 * R + 1)^(d + 1) : ℕ) : ℝ) *
      (4 * Real.pi^2 * ((d + 2 : ℕ) : ℝ) * (R : ℝ)^2 / (n : ℝ)^2) := by
  classical
  calc
    _ ≤ ∑ _p : CoexactPositiveIndex d R × Bool,
        (4 * Real.pi^2 * ((d + 2 : ℕ) : ℝ) * (R : ℝ)^2 / (n : ℝ)^2) := by
      apply Finset.sum_le_sum
      intro p _
      exact positiveCoexact_multiplier_sum_sq_le R p.1
    _ = _ := by simp [CoexactPositiveIndex, Nat.cast_mul, Nat.cast_pow] <;> ring

section Finite
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

theorem actualVolumeMean_numerical_rank (hNc : 2 ≤ Nc) (rho : SUNAdjointModel Nc)
    (R : ℕ) (hR : 2 * R < n) (w : PhysicalGradientIndex (d + 2) n → ℝ)
    (m : ℝ) (hm : 0 ≤ m)
    (hw : ∀ i l, l = 0 ∨ l = Fin.succ 0 →
      ∑ x : FinBox (d + 2) n, max (1 + w (i, (x, l))) 0 ≤ (n : ℝ)^(d + 2) * m)
    (C : PhysicalGaugeOneCochain (d + 2) n Nc → F)
    (L : PhysicalGaugeOneCochain (d + 2) n Nc →L[ℝ] F)
    (hC : HasFDerivAt C L 0) (hC0 : C 0 = 0)
    (Phi : F → ℝ) (K delta radius c : ℝ) (hc : 0 ≤ c)
    (hdelta : 0 < delta) (hradius : 0 < radius)
    (hPhi : ∀ y, ‖y‖ < delta → Phi y ≤ K * ‖y‖^2)
    (hlocal : ∀ A : PhysicalGaugeOneCochain (d + 2) n Nc,
      gaugeConstraintQCLM rho (trivialPhysicalGaugeBackground (d + 2) n Nc) A = 0 →
      ‖A‖ < radius → c * ‖A‖^2 ≤
        inner ℝ A (flatGaugeHodgeK0CLM (d + 2) n Nc rho A) +
        inner ℝ A (componentwiseWeightedRepairCLM w A) + Phi (C A)) :
    c * (((2 * R * (2 * R + 1)^(d + 1) : ℕ) : ℝ) - (finrank ℝ F : ℝ)) ≤
      m * ((2 * R * (2 * R + 1)^(d + 1) : ℕ) : ℝ) *
      (4 * Real.pi^2 * ((d + 2 : ℕ) : ℝ) * (R : ℝ)^2 / (n : ℝ)^2) := by
  have hr := actualVolumeMean_nonlinear_rank hNc rho R hR w m hm hw
    C L hC hC0 Phi K delta radius c hc hdelta hradius hPhi hlocal
  have ht := mul_le_mul_of_nonneg_left (actualPacket_multiplier_trace_le (d := d) (n := n) R) hm
  exact hr.trans (by simpa only [mul_assoc] using ht)
end Finite

section Dilation
variable {d Nc : ℕ} [NeZero Nc]
variable (hNc : 2 ≤ Nc) (rho : SUNAdjointModel Nc) (s R : ℕ)
variable (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
variable (m : ℝ) (hm : 0 ≤ m) (c : ℝ) (hc : 0 < c)
  (hscale : 2 * m * 4 * Real.pi^2 * ((d + 2 : ℕ) : ℝ) /
    ((s + 3 : ℕ) : ℝ)^2 ≤ c)
variable (w : PhysicalGradientIndex (d + 2) ((s + 3) * (R + 1)) → ℝ)
  (hw : ∀ i l, l = 0 ∨ l = Fin.succ 0 →
    ∑ x : FinBox (d + 2) ((s + 3) * (R + 1)), max (1 + w (i, (x, l))) 0 ≤
      (((s + 3) * (R + 1) : ℕ) : ℝ)^(d + 2) * m)
variable (C : PhysicalGaugeOneCochain (d + 2) ((s + 3) * (R + 1)) Nc → F)
  (L : PhysicalGaugeOneCochain (d + 2) ((s + 3) * (R + 1)) Nc →L[ℝ] F)
  (hC : HasFDerivAt C L 0) (hC0 : C 0 = 0)
variable (Phi : F → ℝ) (K delta radius : ℝ) (hdelta : 0 < delta) (hradius : 0 < radius)
  (hPhi : ∀ y, ‖y‖ < delta → Phi y ≤ K * ‖y‖^2)
  (hlocal : ∀ A : PhysicalGaugeOneCochain (d + 2) ((s + 3) * (R + 1)) Nc,
    gaugeConstraintQCLM rho
      (trivialPhysicalGaugeBackground (d + 2) ((s + 3) * (R + 1)) Nc) A = 0 →
    ‖A‖ < radius → c * ‖A‖^2 ≤
      inner ℝ A (flatGaugeHodgeK0CLM (d + 2) ((s + 3) * (R + 1)) Nc rho A) +
      inner ℝ A (componentwiseWeightedRepairCLM w A) + Phi (C A))

include hNc rho m hm c hc hscale w hw C L hC hC0 Phi K delta radius hdelta hradius hPhi hlocal

theorem actualVolumeMean_dilation_density :
    ((2 / ((s + 3 : ℕ) : ℝ))^(d + 2) / 2) *
      (((s + 3) * (R + 1) : ℕ) : ℝ)^(d + 2) ≤ (finrank ℝ F : ℝ) := by
  have hcut : 2 * (R + 1) < (s + 3) * (R + 1) :=
    Nat.mul_lt_mul_of_pos_right (by omega : 2 < s + 3) (by omega)
  have hr := actualVolumeMean_numerical_rank hNc rho (R + 1) hcut w m hm hw
    C L hC hC0 Phi K delta radius c (le_of_lt hc) hdelta hradius hPhi hlocal
  let H : ℝ := ((2 * (R + 1) * (2 * (R + 1) + 1)^(d + 1) : ℕ) : ℝ)
  let B : ℝ := 4 * Real.pi^2 * ((d + 2 : ℕ) : ℝ) * ((R + 1 : ℕ) : ℝ)^2 /
    (((s + 3) * (R + 1) : ℕ) : ℝ)^2
  change c * (H - (finrank ℝ F : ℝ)) ≤ m * H * B at hr
  have he : 2 * m * B = 2 * m * 4 * Real.pi^2 * ((d + 2 : ℕ) : ℝ) /
      ((s + 3 : ℕ) : ℝ)^2 := by
    simpa only [show (1 : ℝ) + (2 * m - 1) = 2 * m by ring] using
      (coexact_dilation_energy_identity d s R (2 * m - 1))
  have hs : 2 * m * B ≤ c := by
    rw [he]
    exact hscale
  have hsH := mul_le_mul_of_nonneg_right hs (show 0 ≤ H by positivity)
  have hhalf : H ≤ 2 * (finrank ℝ F : ℝ) := by
    by_contra hh
    have hp : 0 < c * (H - 2 * (finrank ℝ F : ℝ)) := mul_pos hc (by linarith)
    nlinarith [hsH]
  have hpow : (((2 * (R + 1))^(d + 2) : ℕ) : ℝ) ≤ H := by
    exact_mod_cast coexact_band_power_bound d (R + 1)
  have heq : (2 / ((s + 3 : ℕ) : ℝ))^(d + 2) *
      (((s + 3) * (R + 1) : ℕ) : ℝ)^(d + 2) =
      (((2 * (R + 1) : ℕ) : ℝ))^(d + 2) := by
    rw [← mul_pow]
    congr 1
    have hk : (s : ℝ) + 3 ≠ 0 := by positivity
    push_cast
    field_simp [hk] <;> ring
  have hp := hpow.trans hhalf
  push_cast at hp
  rw [← heq] at hp
  nlinarith
end Dilation

theorem actualVolumeMean_uniform_dilation_density_exists {d Nc : ℕ} [NeZero Nc]
    (hNc : 2 ≤ Nc) (rho : SUNAdjointModel Nc) (m : ℝ) (hm : 0 ≤ m)
    (c : ℝ) (hc : 0 < c) :
    ∃ s : ℕ, ∃ epsilon : ℝ, 0 < epsilon ∧
      ∀ (R : ℕ) (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F]
        [FiniteDimensional ℝ F]
        (w : PhysicalGradientIndex (d + 2) ((s + 3) * (R + 1)) → ℝ)
        (hw : ∀ i l, l = 0 ∨ l = Fin.succ 0 →
          ∑ x : FinBox (d + 2) ((s + 3) * (R + 1)), max (1 + w (i, (x, l))) 0 ≤
            (((s + 3) * (R + 1) : ℕ) : ℝ)^(d + 2) * m)
        (C : PhysicalGaugeOneCochain (d + 2) ((s + 3) * (R + 1)) Nc → F)
        (L : PhysicalGaugeOneCochain (d + 2) ((s + 3) * (R + 1)) Nc →L[ℝ] F)
        (hC : HasFDerivAt C L 0) (hC0 : C 0 = 0) (Phi : F → ℝ)
        (K delta radius : ℝ) (hdelta : 0 < delta) (hradius : 0 < radius)
        (hPhi : ∀ y, ‖y‖ < delta → Phi y ≤ K * ‖y‖^2)
        (hlocal : ∀ A : PhysicalGaugeOneCochain (d + 2) ((s + 3) * (R + 1)) Nc,
          gaugeConstraintQCLM rho
            (trivialPhysicalGaugeBackground (d + 2) ((s + 3) * (R + 1)) Nc) A = 0 →
          ‖A‖ < radius → c * ‖A‖^2 ≤
            inner ℝ A (flatGaugeHodgeK0CLM (d + 2) ((s + 3) * (R + 1)) Nc rho A) +
            inner ℝ A (componentwiseWeightedRepairCLM w A) + Phi (C A)),
        epsilon * (((s + 3) * (R + 1) : ℕ) : ℝ)^(d + 2) ≤ (finrank ℝ F : ℝ) := by
  obtain ⟨s, hs⟩ := coexact_dilation_scale_exists d (2 * m - 1) c hc
  have hscale : 2 * m * 4 * Real.pi^2 * ((d + 2 : ℕ) : ℝ) /
      ((s + 3 : ℕ) : ℝ)^2 ≤ c := by
    have hs' : 2 * m * 4 * Real.pi^2 * ((d + 2 : ℕ) : ℝ) /
        ((s + 3 : ℕ) : ℝ)^2 < c := by
      simpa only [show (1 : ℝ) + (2 * m - 1) = 2 * m by ring] using hs
    exact le_of_lt hs'
  refine ⟨s, (2 / ((s + 3 : ℕ) : ℝ))^(d + 2) / 2, by positivity, ?_⟩
  intro R F _ _ _ w hw C L hC hC0 Phi K delta radius hdelta hradius hPhi hlocal
  exact actualVolumeMean_dilation_density hNc rho s R F m hm c hc hscale w hw
    C L hC hC0 Phi K delta radius hdelta hradius hPhi hlocal
end YangMills.RG
