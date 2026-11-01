import YangMills.RG.ActualPacketSupportEnvelope
import YangMills.RG.PhysicalAverageWeightRank

/-! Full actual packet mean/trace/rank composition. Original local nonlinear
coercivity and occupied positive TOTAL coefficient means remain explicit.
No support, positivity, trace, image dimension or kernel bound is supplied. -/
namespace YangMills.RG
open Module
open scoped BigOperators RealInnerProductSpace
set_option maxHeartbeats 1800000
variable {d n Nc : ℕ} [NeZero n] [NeZero Nc]

theorem actualPacket_envelope_means
    (w : PhysicalGradientIndex (d + 2) n → ℝ) (m : ℝ) (hm : 0 ≤ m)
    (hw : ∀ i l, l = 0 ∨ l = Fin.succ 0 →
      ∑ x : FinBox (d + 2) n, max (1 + w (i, (x, l))) 0 ≤ (n : ℝ)^(d + 2) * m) :
    ∀ i l, ∑ x : FinBox (d + 2) n, actualPacketPositiveEnvelope w (i, (x, l)) ≤
      (n : ℝ)^(d + 2) * m := by
  classical
  intro i l
  by_cases h : l = 0 ∨ l = Fin.succ 0
  · simp only [actualPacketPositiveEnvelope, if_pos h]
    exact hw i l h
  · simp only [actualPacketPositiveEnvelope, if_neg h, Finset.sum_const_zero]
    exact mul_nonneg (pow_nonneg (Nat.cast_nonneg n) _) hm

theorem actualPacketSubspace_finrank (hNc : 2 ≤ Nc) (R : ℕ) (hR : 2 * R < n) :
    finrank ℝ (actualPacketSubspace (n := n) (d := d) hNc R) =
      2 * R * (2 * R + 1) ^ (d + 1) := by
  classical
  have h := (actualPacketBasis (n := n) (d := d) hNc R hR).repr.toLinearEquiv.finrank_eq
  rw [finrank_euclideanSpace] at h
  simpa [CoexactPositiveIndex, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using h

theorem actualPacketSubspace_div_zero (hNc : 2 ≤ Nc) (rho : SUNAdjointModel Nc)
    (R : ℕ) (A : PhysicalGaugeOneCochain (d + 2) n Nc)
    (hA : A ∈ actualPacketSubspace (n := n) (d := d) hNc R) :
    gaugeConstraintQCLM rho (trivialPhysicalGaugeBackground (d + 2) n Nc) A = 0 := by
  rw [actualPacketSubspace_eq_range] at hA
  obtain ⟨c, rfl⟩ := hA
  change gaugeConstraintQCLM rho (trivialPhysicalGaugeBackground (d + 2) n Nc)
    (normalizedCoexactSynthesis (n := n) (d := d) hNc R c) = 0
  exact normalizedCoexactSynthesis_div_zero hNc rho R c

theorem actualPacket_envelope_trace_mean_upper (hNc : 2 ≤ Nc)
    (R : ℕ) (hR : 2 * R < n) (w : PhysicalGradientIndex (d + 2) n → ℝ)
    (m : ℝ) (hm : 0 ≤ m)
    (hw : ∀ i l, l = 0 ∨ l = Fin.succ 0 →
      ∑ x : FinBox (d + 2) n, max (1 + w (i, (x, l))) 0 ≤ (n : ℝ)^(d + 2) * m) :
    LinearMap.trace ℝ (actualPacketSubspace (n := n) (d := d) hNc R)
      (finiteSubspaceCompression (actualPacketSubspace (n := n) (d := d) hNc R)
        (componentwiseWeightedRepairCLM (actualPacketPositiveEnvelope w)).toLinearMap) ≤
      m * ∑ p : CoexactPositiveIndex d R × Bool, ∑ i : Fin (d + 2),
        ‖positiveCoexactCharacter (n := n) (d := d) R p.1
          (Pi.single i (1 : ZMod n)) - 1‖ ^ 2 := by
  classical
  rw [actualPacket_compression_trace hNc R hR]
  calc
    _ ≤ ∑ p : CoexactPositiveIndex d R × Bool, m * ∑ i : Fin (d + 2),
        ‖positiveCoexactCharacter (n := n) (d := d) R p.1
          (Pi.single i (1 : ZMod n)) - 1‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro p _
      exact normalizedRealPacket_mean_upper hNc R hR p _ m
        (actualPacket_envelope_means w m hm hw)
    _ = _ := by rw [Finset.mul_sum]

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

theorem actualVolumeMean_nonlinear_rank (hNc : 2 ≤ Nc) (rho : SUNAdjointModel Nc)
    (R : ℕ) (hR : 2 * R < n) (w : PhysicalGradientIndex (d + 2) n → ℝ)
    (m : ℝ) (hm : 0 ≤ m)
    (hw : ∀ i l, l = 0 ∨ l = Fin.succ 0 →
      ∑ x : FinBox (d + 2) n, max (1 + w (i, (x, l))) 0 ≤ (n : ℝ)^(d + 2) * m)
    (C : PhysicalGaugeOneCochain (d + 2) n Nc → F)
    (L : PhysicalGaugeOneCochain (d + 2) n Nc →L[ℝ] F)
    (hC : HasFDerivAt C L 0) (hC0 : C 0 = 0)
    (Phi : F → ℝ) (K delta radius c : ℝ) (hc : 0 ≤ c)
    (hdelta : 0 < delta) (hradius : 0 < radius)
    (hPhi : ∀ y, ‖y‖ < delta → Phi y ≤ K * ‖y‖ ^ 2)
    (hlocal : ∀ A : PhysicalGaugeOneCochain (d + 2) n Nc,
      gaugeConstraintQCLM rho (trivialPhysicalGaugeBackground (d + 2) n Nc) A = 0 →
      ‖A‖ < radius → c * ‖A‖ ^ 2 ≤
        inner ℝ A (flatGaugeHodgeK0CLM (d + 2) n Nc rho A) +
        inner ℝ A (componentwiseWeightedRepairCLM w A) + Phi (C A)) :
    c * (((2 * R * (2 * R + 1) ^ (d + 1) : ℕ) : ℝ) - (finrank ℝ F : ℝ)) ≤
      m * ∑ p : CoexactPositiveIndex d R × Bool, ∑ i : Fin (d + 2),
        ‖positiveCoexactCharacter (n := n) (d := d) R p.1
          (Pi.single i (1 : ZMod n)) - 1‖ ^ 2 := by
  have hr := local_nonlinear_compressed_trace_rank_bound
    (actualPacketSubspace (n := n) (d := d) hNc R)
    (componentwiseWeightedRepairCLM (actualPacketPositiveEnvelope w)).toLinearMap
    (fun A _ => actualPacket_envelope_form_nonneg w A)
    C L hC hC0 Phi K delta radius c hc hdelta hradius hPhi (by
      intro A hA hnorm
      have hdiv := actualPacketSubspace_div_zero hNc rho R A hA
      exact (hlocal A hdiv hnorm).trans
        (add_le_add_right (actualPacket_envelope_order hNc rho R w A hA) (Phi (C A))))
  rw [actualPacketSubspace_finrank hNc R hR] at hr
  exact hr.trans (actualPacket_envelope_trace_mean_upper hNc R hR w m hm hw)

end YangMills.RG
