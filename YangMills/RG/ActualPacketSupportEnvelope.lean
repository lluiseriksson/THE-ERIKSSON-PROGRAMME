import YangMills.RG.ActualPacketCompression
import YangMills.RG.ComponentwiseFlatHodge

/-! Whole-image support and a constructed positive total-stiffness envelope.
The original weights have no sign/lower bound; order is proved only on the
actual packet image, not assumed globally. -/
namespace YangMills.RG
open scoped BigOperators RealInnerProductSpace
set_option maxHeartbeats 1600000
variable {d n Nc : ℕ} [NeZero n] [NeZero Nc]

theorem actualPacket_support (hNc : 2 ≤ Nc) (R : ℕ)
    (A : PhysicalGaugeOneCochain (d + 2) n Nc)
    (hA : A ∈ actualPacketSubspace (n := n) (d := d) hNc R)
    (x : FinBox (d + 2) n) (l : Fin (d + 2))
    (h0 : l ≠ 0) (h1 : l ≠ Fin.succ 0) : A (x, l) = 0 := by
  rw [actualPacketSubspace_eq_range] at hA
  obtain ⟨c, rfl⟩ := hA
  change (coexactFlatMap hNc (0 : Fin (d + 2)) (Fin.succ 0)
    (normalizedScalarSynthesisReal (n := n) (d := d) R c)) (x, l) = 0
  rw [coexactFlatMap_apply]
  simp only [PiLp.sub_apply, torusPhysicalEmbed, PiLp.toLp_apply, if_neg h0, if_neg h1, sub_self]

theorem actualPacket_gradient_zero (hNc : 2 ≤ Nc) (R : ℕ)
    (A : PhysicalGaugeOneCochain (d + 2) n Nc)
    (hA : A ∈ actualPacketSubspace (n := n) (d := d) hNc R)
    (i : Fin (d + 2)) (x : FinBox (d + 2) n) (l : Fin (d + 2))
    (h0 : l ≠ 0) (h1 : l ≠ Fin.succ 0) :
    A (x.shift i, l) - A (x, l) = 0 := by
  rw [actualPacket_support hNc R A hA (x.shift i) l h0 h1,
    actualPacket_support hNc R A hA x l h0 h1, sub_self]

theorem actualTotalStiffness_energy (rho : SUNAdjointModel Nc)
    (w : PhysicalGradientIndex (d + 2) n → ℝ)
    (A : PhysicalGaugeOneCochain (d + 2) n Nc) :
    inner ℝ A (flatGaugeHodgeK0CLM (d + 2) n Nc rho A) +
      inner ℝ A (componentwiseWeightedRepairCLM w A) =
    ∑ p : PhysicalGradientIndex (d + 2) n,
      (1 + w p) * ‖A ((p.2.1).shift p.1, p.2.2) - A p.2‖ ^ 2 := by
  rw [← componentwiseFlatGradient_eq_hodge rho A,
    componentwiseFlatGradient_energy, componentwiseWeightedRepair_energy,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p _
  ring

noncomputable def actualPacketPositiveEnvelope
    (w : PhysicalGradientIndex (d + 2) n → ℝ) :
    PhysicalGradientIndex (d + 2) n → ℝ := fun p =>
  if p.2.2 = 0 ∨ p.2.2 = Fin.succ 0 then max (1 + w p) 0 else 0

theorem actualPacketPositiveEnvelope_nonneg
    (w : PhysicalGradientIndex (d + 2) n → ℝ)
    (p : PhysicalGradientIndex (d + 2) n) :
    0 ≤ actualPacketPositiveEnvelope w p := by
  classical
  unfold actualPacketPositiveEnvelope
  split_ifs
  · exact le_max_right _ _
  · exact le_rfl

theorem actualPacket_envelope_order (hNc : 2 ≤ Nc) (rho : SUNAdjointModel Nc)
    (R : ℕ) (w : PhysicalGradientIndex (d + 2) n → ℝ)
    (A : PhysicalGaugeOneCochain (d + 2) n Nc)
    (hA : A ∈ actualPacketSubspace (n := n) (d := d) hNc R) :
    inner ℝ A (flatGaugeHodgeK0CLM (d + 2) n Nc rho A) +
      inner ℝ A (componentwiseWeightedRepairCLM w A) ≤
    inner ℝ A (componentwiseWeightedRepairCLM (actualPacketPositiveEnvelope w) A) := by
  classical
  rw [actualTotalStiffness_energy, componentwiseWeightedRepair_energy]
  apply Finset.sum_le_sum
  intro p _
  by_cases h : p.2.2 = 0 ∨ p.2.2 = Fin.succ 0
  · rw [actualPacketPositiveEnvelope, if_pos h]
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _)
  · have hz := actualPacket_gradient_zero hNc R A hA p.1 p.2.1 p.2.2
      (not_or.mp h).1 (not_or.mp h).2
    rw [hz]
    simp

theorem actualPacket_envelope_form_nonneg
    (w : PhysicalGradientIndex (d + 2) n → ℝ)
    (A : PhysicalGaugeOneCochain (d + 2) n Nc) :
    0 ≤ inner ℝ A
      (componentwiseWeightedRepairCLM (actualPacketPositiveEnvelope w) A) := by
  exact componentwiseWeightedRepair_nonneg _ (actualPacketPositiveEnvelope_nonneg w) A

end YangMills.RG
