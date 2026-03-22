import Mathlib
import YangMills.ClayCore.BalabanRG.BalabanRGUniformLSIQuantitativeP81ObstructionCoherence
import YangMills.ClayCore.BalabanRG.BalabanRGUniformLSIQuantitativeP81ThresholdOneObstructionPacket

namespace YangMills.ClayCore

open scoped BigOperators
open Classical
noncomputable section

/-- Bridge from the explicit threshold-one obstruction surface to the standard quantitative P81
obstruction packet and coherence hub. -/
def BalabanRGUniformLSIQuantitativeP81ThresholdOneObstructionBridge
    (d N_c : ℕ) [NeZero N_c] [∀ k, ActivityNorm d k] : Prop :=
  BalabanRGUniformLSIQuantitativeP81ThresholdOneObstructionPacket d N_c

/-- Canonical bridge from the threshold-one obstruction packet. -/
theorem balaban_rg_uniform_lsi_quantitative_p81_threshold_one_obstruction_bridge_of_threshold_one_obstruction_packet
    (d N_c : ℕ) [NeZero N_c] [∀ k, ActivityNorm d k]
    (packet : BalabanRGUniformLSIQuantitativeP81ThresholdOneObstructionPacket d N_c) :
    BalabanRGUniformLSIQuantitativeP81ThresholdOneObstructionBridge d N_c := by
  exact packet

/-- Canonical bridge from the direct quantitative frontier together with the theorem-side live
target. -/
theorem balaban_rg_uniform_lsi_quantitative_p81_threshold_one_obstruction_bridge_of_quantitative_frontier_and_live_target
    (d N_c : ℕ) [NeZero N_c] [∀ k, ActivityNorm d k]
    (frontier : BalabanRGUniformLSIQuantitativeFrontier d N_c)
    (live : RGCauchyP81LiveTarget d N_c) :
    BalabanRGUniformLSIQuantitativeP81ThresholdOneObstructionBridge d N_c := by
  exact
    balaban_rg_uniform_lsi_quantitative_p81_threshold_one_obstruction_packet_of_quantitative_frontier_and_live_target
      d N_c frontier live

/-- Projection back to the explicit threshold-one obstruction packet. -/
theorem threshold_one_obstruction_packet_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_obstruction_bridge
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (bridge : BalabanRGUniformLSIQuantitativeP81ThresholdOneObstructionBridge d N_c) :
    BalabanRGUniformLSIQuantitativeP81ThresholdOneObstructionPacket d N_c := by
  exact bridge

/-- Standard quantitative P81 obstruction packet reconstructed from the bridge. -/
theorem quantitative_p81_obstruction_packet_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_obstruction_bridge
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (bridge : BalabanRGUniformLSIQuantitativeP81ThresholdOneObstructionBridge d N_c) :
    BalabanRGUniformLSIQuantitativeP81ObstructionPacket d N_c := by
  exact
    balaban_rg_uniform_lsi_quantitative_p81_obstruction_packet_of_quantitative_frontier_and_live_target
      d N_c
      (quantitative_frontier_of_balaban_rg_uniform_lsi_quantitative_p81_kernel_packet
        (quantitative_p81_kernel_packet_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_packet
          (threshold_one_packet_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_obstruction_packet
            (threshold_one_obstruction_packet_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_obstruction_bridge
              bridge))))
      (theorem_live_target_of_balaban_rg_uniform_lsi_quantitative_p81_kernel_packet
        (quantitative_p81_kernel_packet_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_packet
          (threshold_one_packet_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_obstruction_packet
            (threshold_one_obstruction_packet_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_obstruction_bridge
              bridge))))

/-- Standard quantitative P81 obstruction coherence hub reconstructed from the bridge. -/
theorem quantitative_p81_obstruction_coherence_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_obstruction_bridge
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (bridge : BalabanRGUniformLSIQuantitativeP81ThresholdOneObstructionBridge d N_c) :
    BalabanRGUniformLSIQuantitativeP81ObstructionCoherence d N_c := by
  exact
    balaban_rg_uniform_lsi_quantitative_p81_obstruction_coherence_of_quantitative_p81_obstruction_packet
      d N_c
      (quantitative_p81_obstruction_packet_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_obstruction_bridge
        bridge)

/-- Bridge coherence: the standard existential increment-decay obstruction surface agrees
canonically with the explicit threshold-one obstruction surface. -/
theorem rg_increment_decay_bound_eq_threshold_one_canonical_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_obstruction_bridge
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (bridge : BalabanRGUniformLSIQuantitativeP81ThresholdOneObstructionBridge d N_c) :
    rg_increment_decay_bound_of_balaban_rg_uniform_lsi_quantitative_p81_obstruction_packet
        (quantitative_p81_obstruction_packet_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_obstruction_bridge
          bridge)
      =
      rg_increment_decay_bound_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_obstruction_packet
        (threshold_one_obstruction_packet_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_obstruction_bridge
          bridge) := by
  apply Subsingleton.elim

/-- Bridge coherence: the standard existential RG-Cauchy summability obstruction surface agrees
canonically with the explicit threshold-one obstruction surface. -/
theorem rg_cauchy_summability_bound_eq_threshold_one_canonical_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_obstruction_bridge
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (bridge : BalabanRGUniformLSIQuantitativeP81ThresholdOneObstructionBridge d N_c) :
    rg_cauchy_summability_bound_of_balaban_rg_uniform_lsi_quantitative_p81_obstruction_packet
        (quantitative_p81_obstruction_packet_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_obstruction_bridge
          bridge)
      =
      rg_cauchy_summability_bound_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_obstruction_packet
        (threshold_one_obstruction_packet_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_obstruction_bridge
          bridge) := by
  apply Subsingleton.elim

/-- Bridge coherence: the theorem-side live target inside the standard quantitative obstruction
packet agrees canonically with the threshold-one live target carried by the explicit endpoint. -/
theorem theorem_live_target_eq_threshold_one_canonical_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_obstruction_bridge
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (bridge : BalabanRGUniformLSIQuantitativeP81ThresholdOneObstructionBridge d N_c) :
    theorem_live_target_of_balaban_rg_uniform_lsi_quantitative_p81_obstruction_packet
        (quantitative_p81_obstruction_packet_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_obstruction_bridge
          bridge)
      =
      rg_cauchy_p81_threshold_one_live_target_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_packet
        (threshold_one_packet_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_obstruction_packet
          (threshold_one_obstruction_packet_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_obstruction_bridge
            bridge)) := by
  apply Subsingleton.elim

/-- Bridge coherence: the short public P81 frontier inside the standard quantitative obstruction
packet agrees canonically with the explicit threshold-one frontier. -/
theorem rg_cauchy_p81_frontier_eq_threshold_one_canonical_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_obstruction_bridge
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (bridge : BalabanRGUniformLSIQuantitativeP81ThresholdOneObstructionBridge d N_c) :
    rg_cauchy_p81_frontier_of_balaban_rg_uniform_lsi_quantitative_p81_obstruction_packet
        (quantitative_p81_obstruction_packet_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_obstruction_bridge
          bridge)
      =
      rg_cauchy_p81_frontier_at_one_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_packet
        (threshold_one_packet_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_obstruction_packet
          (threshold_one_obstruction_packet_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_obstruction_bridge
            bridge)) := by
  apply Subsingleton.elim

/-- Bridge coherence: the audit-link inside the standard quantitative obstruction packet agrees
canonically with the explicit threshold-one audit-link. -/
theorem balaban_rg_uniform_lsi_rg_cauchy_audit_link_eq_threshold_one_canonical_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_obstruction_bridge
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (bridge : BalabanRGUniformLSIQuantitativeP81ThresholdOneObstructionBridge d N_c) :
    balaban_rg_uniform_lsi_rg_cauchy_audit_link_of_balaban_rg_uniform_lsi_quantitative_p81_obstruction_packet
        (quantitative_p81_obstruction_packet_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_obstruction_bridge
          bridge)
      =
      balaban_rg_uniform_lsi_rg_cauchy_audit_link_at_one_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_packet
        (threshold_one_packet_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_obstruction_packet
          (threshold_one_obstruction_packet_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_obstruction_bridge
            bridge)) := by
  apply Subsingleton.elim

/-- Bridge coherence: the theorem-side coherence packet inside the standard quantitative
obstruction packet agrees canonically with the explicit threshold-one coherence packet. -/
theorem rg_cauchy_p81_coherence_packet_eq_threshold_one_canonical_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_obstruction_bridge
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (bridge : BalabanRGUniformLSIQuantitativeP81ThresholdOneObstructionBridge d N_c) :
    rg_cauchy_p81_coherence_packet_of_balaban_rg_uniform_lsi_quantitative_p81_obstruction_packet
        (quantitative_p81_obstruction_packet_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_obstruction_bridge
          bridge)
      =
      rg_cauchy_p81_coherence_packet_at_one_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_packet
        (threshold_one_packet_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_obstruction_packet
          (threshold_one_obstruction_packet_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_obstruction_bridge
            bridge)) := by
  apply Subsingleton.elim

/-- Bridge coherence: the obligation surface inside the standard quantitative obstruction packet
agrees canonically with the explicit threshold-one obligation. -/
theorem obligation_eq_threshold_one_canonical_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_obstruction_bridge
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (bridge : BalabanRGUniformLSIQuantitativeP81ThresholdOneObstructionBridge d N_c) :
    obligation_of_balaban_rg_uniform_lsi_quantitative_p81_obstruction_packet
        (quantitative_p81_obstruction_packet_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_obstruction_bridge
          bridge)
      =
      rg_cauchy_p81_obligation_at_one_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_packet
        (threshold_one_packet_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_obstruction_packet
          (threshold_one_obstruction_packet_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_obstruction_bridge
            bridge)) := by
  apply Subsingleton.elim

/-- Bridge coherence: the kernel input packet inside the standard quantitative obstruction packet
agrees canonically with the explicit threshold-one kernel input. -/
theorem rg_cauchy_p81_kernel_input_eq_threshold_one_canonical_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_obstruction_bridge
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (bridge : BalabanRGUniformLSIQuantitativeP81ThresholdOneObstructionBridge d N_c) :
    rg_cauchy_p81_kernel_input_of_balaban_rg_uniform_lsi_quantitative_p81_obstruction_packet
        (quantitative_p81_obstruction_packet_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_obstruction_bridge
          bridge)
      =
      rg_cauchy_p81_kernel_input_at_one_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_packet
        (threshold_one_packet_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_obstruction_packet
          (threshold_one_obstruction_packet_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_obstruction_bridge
            bridge)) := by
  apply Subsingleton.elim

/-- Bridge coherence: the kernel output packet inside the standard quantitative obstruction packet
agrees canonically with the explicit threshold-one kernel output. -/
theorem rg_cauchy_p81_kernel_output_eq_threshold_one_canonical_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_obstruction_bridge
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (bridge : BalabanRGUniformLSIQuantitativeP81ThresholdOneObstructionBridge d N_c) :
    rg_cauchy_p81_kernel_output_of_balaban_rg_uniform_lsi_quantitative_p81_obstruction_packet
        (quantitative_p81_obstruction_packet_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_obstruction_bridge
          bridge)
      =
      rg_cauchy_p81_kernel_output_at_one_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_packet
        (threshold_one_packet_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_obstruction_packet
          (threshold_one_obstruction_packet_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_obstruction_bridge
            bridge)) := by
  apply Subsingleton.elim

/-- Logical normal form: the threshold-one obstruction bridge is equivalent to the explicit
threshold-one obstruction packet. -/
theorem balaban_rg_uniform_lsi_quantitative_p81_threshold_one_obstruction_bridge_iff_threshold_one_obstruction_packet
    (d N_c : ℕ) [NeZero N_c] [∀ k, ActivityNorm d k] :
    BalabanRGUniformLSIQuantitativeP81ThresholdOneObstructionBridge d N_c ↔
      BalabanRGUniformLSIQuantitativeP81ThresholdOneObstructionPacket d N_c := by
  constructor
  · intro bridge
    exact bridge
  · intro packet
    exact packet

/-- Logical normal form: the threshold-one obstruction bridge is equivalent to the pair
consisting of the direct quantitative frontier and the theorem-side live target. -/
theorem balaban_rg_uniform_lsi_quantitative_p81_threshold_one_obstruction_bridge_iff_quantitative_frontier_and_live_target
    (d N_c : ℕ) [NeZero N_c] [∀ k, ActivityNorm d k] :
    BalabanRGUniformLSIQuantitativeP81ThresholdOneObstructionBridge d N_c ↔
      (BalabanRGUniformLSIQuantitativeFrontier d N_c ∧ RGCauchyP81LiveTarget d N_c) := by
  constructor
  · intro bridge
    exact
      ⟨ quantitative_frontier_of_balaban_rg_uniform_lsi_quantitative_p81_kernel_packet
            (quantitative_p81_kernel_packet_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_packet
              (threshold_one_packet_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_obstruction_packet
                (threshold_one_obstruction_packet_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_obstruction_bridge
                  bridge))),
        theorem_live_target_of_balaban_rg_uniform_lsi_quantitative_p81_kernel_packet
            (quantitative_p81_kernel_packet_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_packet
              (threshold_one_packet_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_obstruction_packet
                (threshold_one_obstruction_packet_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_obstruction_bridge
                  bridge))) ⟩
  · intro h
    exact
      balaban_rg_uniform_lsi_quantitative_p81_threshold_one_obstruction_bridge_of_quantitative_frontier_and_live_target
        d N_c h.1 h.2

end

end YangMills.ClayCore
