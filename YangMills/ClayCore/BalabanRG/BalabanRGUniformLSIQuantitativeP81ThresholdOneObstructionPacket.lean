import Mathlib
import YangMills.ClayCore.BalabanRG.BalabanRGUniformLSIQuantitativeP81ThresholdOnePacket

namespace YangMills.ClayCore

open scoped BigOperators
open Classical
noncomputable section

/-- Explicit theorem-side obstruction packet obtained from the threshold-one (`β = 1`) endpoint
of the quantitative P81 route. -/
structure BalabanRGUniformLSIQuantitativeP81ThresholdOneObstructionPacket
    (d N_c : ℕ) [NeZero N_c] [∀ k, ActivityNorm d k] : Prop where
  thresholdOnePacket : BalabanRGUniformLSIQuantitativeP81ThresholdOnePacket d N_c
  incrementDecayBound : ∃ β : ℝ, 1 ≤ β ∧ RGIncrementDecayBound d N_c β
  cauchySummabilityBound : ∃ β : ℝ, 1 ≤ β ∧ RGCauchySummabilityBound d N_c β

/-- Canonical threshold-one obstruction packet from the threshold-one packet. -/
theorem balaban_rg_uniform_lsi_quantitative_p81_threshold_one_obstruction_packet_of_threshold_one_packet
    (d N_c : ℕ) [NeZero N_c] [∀ k, ActivityNorm d k]
    (packet : BalabanRGUniformLSIQuantitativeP81ThresholdOnePacket d N_c) :
    BalabanRGUniformLSIQuantitativeP81ThresholdOneObstructionPacket d N_c := by
  exact
    ⟨ packet,
      ⟨1, le_rfl,
        rg_increment_decay_P81_at_one_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_packet packet⟩,
      ⟨1, le_rfl,
        rg_cauchy_from_increment_decay_at_one_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_packet packet⟩ ⟩

/-- Canonical threshold-one obstruction packet from the direct quantitative frontier together
with the theorem-side live target. -/
theorem balaban_rg_uniform_lsi_quantitative_p81_threshold_one_obstruction_packet_of_quantitative_frontier_and_live_target
    (d N_c : ℕ) [NeZero N_c] [∀ k, ActivityNorm d k]
    (frontier : BalabanRGUniformLSIQuantitativeFrontier d N_c)
    (live : RGCauchyP81LiveTarget d N_c) :
    BalabanRGUniformLSIQuantitativeP81ThresholdOneObstructionPacket d N_c := by
  exact
    balaban_rg_uniform_lsi_quantitative_p81_threshold_one_obstruction_packet_of_threshold_one_packet
      d N_c
      (balaban_rg_uniform_lsi_quantitative_p81_threshold_one_packet_of_quantitative_frontier_and_live_target
        d N_c frontier live)

/-- Projection to the threshold-one packet. -/
theorem threshold_one_packet_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_obstruction_packet
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (packet : BalabanRGUniformLSIQuantitativeP81ThresholdOneObstructionPacket d N_c) :
    BalabanRGUniformLSIQuantitativeP81ThresholdOnePacket d N_c := by
  exact packet.thresholdOnePacket

/-- Projection to the standard existential increment-decay obstruction surface. -/
theorem rg_increment_decay_bound_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_obstruction_packet
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (packet : BalabanRGUniformLSIQuantitativeP81ThresholdOneObstructionPacket d N_c) :
    ∃ β : ℝ, 1 ≤ β ∧ RGIncrementDecayBound d N_c β := by
  exact packet.incrementDecayBound

/-- Projection to the standard existential RG-Cauchy summability obstruction surface. -/
theorem rg_cauchy_summability_bound_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_obstruction_packet
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (packet : BalabanRGUniformLSIQuantitativeP81ThresholdOneObstructionPacket d N_c) :
    ∃ β : ℝ, 1 ≤ β ∧ RGCauchySummabilityBound d N_c β := by
  exact packet.cauchySummabilityBound

/-- Explicit threshold-one witness for the existential increment-decay obstruction surface. -/
theorem explicit_threshold_one_increment_decay_witness_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_obstruction_packet
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (packet : BalabanRGUniformLSIQuantitativeP81ThresholdOneObstructionPacket d N_c) :
    ∃ β : ℝ, 1 ≤ β ∧ RGIncrementDecayBound d N_c β := by
  exact
    ⟨1, le_rfl,
      rg_increment_decay_P81_at_one_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_packet
        (threshold_one_packet_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_obstruction_packet
          packet)⟩

/-- Explicit threshold-one witness for the existential RG-Cauchy summability obstruction
surface. -/
theorem explicit_threshold_one_cauchy_witness_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_obstruction_packet
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (packet : BalabanRGUniformLSIQuantitativeP81ThresholdOneObstructionPacket d N_c) :
    ∃ β : ℝ, 1 ≤ β ∧ RGCauchySummabilityBound d N_c β := by
  exact
    ⟨1, le_rfl,
      rg_cauchy_from_increment_decay_at_one_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_packet
        (threshold_one_packet_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_obstruction_packet
          packet)⟩

/-- Coherence: the existential increment-decay obstruction surface agrees canonically with the
explicit threshold-one witness. -/
theorem rg_increment_decay_bound_eq_threshold_one_witness_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_obstruction_packet
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (packet : BalabanRGUniformLSIQuantitativeP81ThresholdOneObstructionPacket d N_c) :
    rg_increment_decay_bound_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_obstruction_packet packet =
      explicit_threshold_one_increment_decay_witness_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_obstruction_packet packet := by
  apply Subsingleton.elim

/-- Coherence: the existential RG-Cauchy summability obstruction surface agrees canonically with
the explicit threshold-one witness. -/
theorem rg_cauchy_summability_bound_eq_threshold_one_witness_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_obstruction_packet
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (packet : BalabanRGUniformLSIQuantitativeP81ThresholdOneObstructionPacket d N_c) :
    rg_cauchy_summability_bound_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_obstruction_packet packet =
      explicit_threshold_one_cauchy_witness_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_obstruction_packet packet := by
  apply Subsingleton.elim

/-- Coherence: the existential increment-decay obstruction surface agrees canonically with the
standard existential surface reconstructed from the theorem-side live target. -/
theorem rg_increment_decay_bound_eq_canonical_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_obstruction_packet
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (packet : BalabanRGUniformLSIQuantitativeP81ThresholdOneObstructionPacket d N_c) :
    rg_increment_decay_bound_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_obstruction_packet packet =
      rg_increment_decay_bound_of_rg_cauchy_p81_live_target
        (rg_cauchy_p81_threshold_one_live_target_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_packet
          (threshold_one_packet_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_obstruction_packet
            packet)) := by
  apply Subsingleton.elim

/-- Coherence: the existential RG-Cauchy summability obstruction surface agrees canonically with
the standard existential surface reconstructed from the theorem-side live target. -/
theorem rg_cauchy_summability_bound_eq_canonical_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_obstruction_packet
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (packet : BalabanRGUniformLSIQuantitativeP81ThresholdOneObstructionPacket d N_c) :
    rg_cauchy_summability_bound_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_obstruction_packet packet =
      rg_cauchy_summability_bound_of_rg_cauchy_p81_live_target
        (rg_cauchy_p81_threshold_one_live_target_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_packet
          (threshold_one_packet_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_obstruction_packet
            packet)) := by
  apply Subsingleton.elim

/-- Logical normal form: the threshold-one obstruction packet is equivalent to the threshold-one
packet. -/
theorem balaban_rg_uniform_lsi_quantitative_p81_threshold_one_obstruction_packet_iff_threshold_one_packet
    (d N_c : ℕ) [NeZero N_c] [∀ k, ActivityNorm d k] :
    BalabanRGUniformLSIQuantitativeP81ThresholdOneObstructionPacket d N_c ↔
      BalabanRGUniformLSIQuantitativeP81ThresholdOnePacket d N_c := by
  constructor
  · intro packet
    exact packet.thresholdOnePacket
  · intro packet
    exact
      balaban_rg_uniform_lsi_quantitative_p81_threshold_one_obstruction_packet_of_threshold_one_packet
        d N_c packet

/-- Logical normal form: the threshold-one obstruction packet is equivalent to the pair
consisting of the direct quantitative frontier and the theorem-side live target. -/
theorem balaban_rg_uniform_lsi_quantitative_p81_threshold_one_obstruction_packet_iff_quantitative_frontier_and_live_target
    (d N_c : ℕ) [NeZero N_c] [∀ k, ActivityNorm d k] :
    BalabanRGUniformLSIQuantitativeP81ThresholdOneObstructionPacket d N_c ↔
      (BalabanRGUniformLSIQuantitativeFrontier d N_c ∧ RGCauchyP81LiveTarget d N_c) := by
  constructor
  · intro packet
    exact
      ⟨ quantitative_frontier_of_balaban_rg_uniform_lsi_quantitative_p81_kernel_packet
            (quantitative_p81_kernel_packet_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_packet
              (threshold_one_packet_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_obstruction_packet
                packet)),
        theorem_live_target_of_balaban_rg_uniform_lsi_quantitative_p81_kernel_packet
            (quantitative_p81_kernel_packet_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_packet
              (threshold_one_packet_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_obstruction_packet
                packet)) ⟩
  · intro h
    exact
      balaban_rg_uniform_lsi_quantitative_p81_threshold_one_obstruction_packet_of_quantitative_frontier_and_live_target
        d N_c h.1 h.2

end

end YangMills.ClayCore
