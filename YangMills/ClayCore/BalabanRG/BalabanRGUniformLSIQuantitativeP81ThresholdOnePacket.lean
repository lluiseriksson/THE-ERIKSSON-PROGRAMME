import Mathlib
import YangMills.ClayCore.BalabanRG.BalabanRGUniformLSIQuantitativeP81ThresholdOneFrontierBridge

namespace YangMills.ClayCore

open scoped BigOperators
open Classical
noncomputable section

/-- Explicit theorem-side packet for the threshold-one (`β = 1`) endpoint of the quantitative
P81 route. -/
structure BalabanRGUniformLSIQuantitativeP81ThresholdOnePacket
    (d N_c : ℕ) [NeZero N_c] [∀ k, ActivityNorm d k] : Prop where
  thresholdOneFrontierBridge : BalabanRGUniformLSIQuantitativeP81ThresholdOneFrontierBridge d N_c
  thresholdOneBridge : BalabanRGUniformLSIQuantitativeP81ThresholdOneBridge d N_c
  canonicalLiveTargetBridge : BalabanRGUniformLSIQuantitativeP81CanonicalLiveTargetBridge d N_c
  interfaceBridge : BalabanRGUniformLSIQuantitativeP81InterfaceBridge d N_c
  quantitativeP81KernelPacket : BalabanRGUniformLSIQuantitativeP81KernelPacket d N_c
  standardAuditPacket : BalabanRGUniformLSIAuditPacket d N_c
  incrementDecayAtOne : RGIncrementDecayBound d N_c 1
  cauchyAtOne : RGCauchySummabilityBound d N_c 1
  liveTarget : RGCauchyP81LiveTarget d N_c
  kernelOutput : RGCauchyP81KernelOutput d N_c
  kernelInput : RGCauchyP81KernelInput d N_c
  obligation : RGCauchyP81Obligation d N_c
  frontier : RGCauchyP81Frontier d N_c
  auditLink : BalabanRGUniformLSIRGCauchyAuditLink d N_c
  coherencePacket : RGCauchyP81CoherencePacket d N_c

/-- Canonical threshold-one packet from the threshold-one frontier bridge. -/
theorem balaban_rg_uniform_lsi_quantitative_p81_threshold_one_packet_of_threshold_one_frontier_bridge
    (d N_c : ℕ) [NeZero N_c] [∀ k, ActivityNorm d k]
    (bridge : BalabanRGUniformLSIQuantitativeP81ThresholdOneFrontierBridge d N_c) :
    BalabanRGUniformLSIQuantitativeP81ThresholdOnePacket d N_c := by
  exact
    ⟨ bridge,
      threshold_one_bridge_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_frontier_bridge bridge,
      quantitative_p81_canonical_live_target_bridge_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_bridge
        (threshold_one_bridge_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_frontier_bridge bridge),
      quantitative_p81_interface_bridge_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_bridge
        (threshold_one_bridge_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_frontier_bridge bridge),
      quantitative_p81_kernel_packet_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_frontier_bridge bridge,
      standard_audit_packet_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_frontier_bridge bridge,
      rg_increment_decay_P81_at_one_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_bridge
        (threshold_one_bridge_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_frontier_bridge bridge),
      rg_cauchy_from_increment_decay_at_one_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_bridge
        (threshold_one_bridge_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_frontier_bridge bridge),
      rg_cauchy_p81_threshold_one_live_target_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_bridge
        (threshold_one_bridge_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_frontier_bridge bridge),
      rg_cauchy_p81_kernel_output_at_one_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_bridge
        (threshold_one_bridge_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_frontier_bridge bridge),
      rg_cauchy_p81_kernel_input_at_one_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_bridge
        (threshold_one_bridge_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_frontier_bridge bridge),
      rg_cauchy_p81_obligation_at_one_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_bridge
        (threshold_one_bridge_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_frontier_bridge bridge),
      rg_cauchy_p81_frontier_at_one_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_frontier_bridge bridge,
      balaban_rg_uniform_lsi_rg_cauchy_audit_link_at_one_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_frontier_bridge bridge,
      rg_cauchy_p81_coherence_packet_at_one_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_frontier_bridge bridge ⟩

/-- Canonical threshold-one packet from the direct quantitative frontier together with the
theorem-side live target. -/
theorem balaban_rg_uniform_lsi_quantitative_p81_threshold_one_packet_of_quantitative_frontier_and_live_target
    (d N_c : ℕ) [NeZero N_c] [∀ k, ActivityNorm d k]
    (frontier : BalabanRGUniformLSIQuantitativeFrontier d N_c)
    (live : RGCauchyP81LiveTarget d N_c) :
    BalabanRGUniformLSIQuantitativeP81ThresholdOnePacket d N_c := by
  exact
    balaban_rg_uniform_lsi_quantitative_p81_threshold_one_packet_of_threshold_one_frontier_bridge
      d N_c
      (balaban_rg_uniform_lsi_quantitative_p81_threshold_one_frontier_bridge_of_quantitative_frontier_and_live_target
        d N_c frontier live)

/-- Projection to the threshold-one frontier bridge. -/
theorem threshold_one_frontier_bridge_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_packet
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (packet : BalabanRGUniformLSIQuantitativeP81ThresholdOnePacket d N_c) :
    BalabanRGUniformLSIQuantitativeP81ThresholdOneFrontierBridge d N_c := by
  exact packet.thresholdOneFrontierBridge

/-- Projection to the threshold-one bridge. -/
theorem threshold_one_bridge_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_packet
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (packet : BalabanRGUniformLSIQuantitativeP81ThresholdOnePacket d N_c) :
    BalabanRGUniformLSIQuantitativeP81ThresholdOneBridge d N_c := by
  exact packet.thresholdOneBridge

/-- Projection to the canonical live-target bridge. -/
theorem canonical_live_target_bridge_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_packet
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (packet : BalabanRGUniformLSIQuantitativeP81ThresholdOnePacket d N_c) :
    BalabanRGUniformLSIQuantitativeP81CanonicalLiveTargetBridge d N_c := by
  exact packet.canonicalLiveTargetBridge

/-- Projection to the interface bridge. -/
theorem interface_bridge_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_packet
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (packet : BalabanRGUniformLSIQuantitativeP81ThresholdOnePacket d N_c) :
    BalabanRGUniformLSIQuantitativeP81InterfaceBridge d N_c := by
  exact packet.interfaceBridge

/-- Projection to the quantitative P81 kernel packet. -/
theorem quantitative_p81_kernel_packet_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_packet
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (packet : BalabanRGUniformLSIQuantitativeP81ThresholdOnePacket d N_c) :
    BalabanRGUniformLSIQuantitativeP81KernelPacket d N_c := by
  exact packet.quantitativeP81KernelPacket

/-- Projection to the standard audit packet attached to the threshold-one route. -/
theorem standard_audit_packet_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_packet
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (packet : BalabanRGUniformLSIQuantitativeP81ThresholdOnePacket d N_c) :
    BalabanRGUniformLSIAuditPacket d N_c := by
  exact packet.standardAuditPacket

/-- Projection to the explicit threshold-one increment-decay statement. -/
theorem rg_increment_decay_P81_at_one_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_packet
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (packet : BalabanRGUniformLSIQuantitativeP81ThresholdOnePacket d N_c) :
    RGIncrementDecayBound d N_c 1 := by
  exact packet.incrementDecayAtOne

/-- Projection to the explicit threshold-one summability statement. -/
theorem rg_cauchy_from_increment_decay_at_one_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_packet
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (packet : BalabanRGUniformLSIQuantitativeP81ThresholdOnePacket d N_c) :
    RGCauchySummabilityBound d N_c 1 := by
  exact packet.cauchyAtOne

/-- Projection to the threshold-one theorem-side live target. -/
theorem rg_cauchy_p81_threshold_one_live_target_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_packet
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (packet : BalabanRGUniformLSIQuantitativeP81ThresholdOnePacket d N_c) :
    RGCauchyP81LiveTarget d N_c := by
  exact packet.liveTarget

/-- Projection to the threshold-one kernel output. -/
theorem rg_cauchy_p81_kernel_output_at_one_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_packet
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (packet : BalabanRGUniformLSIQuantitativeP81ThresholdOnePacket d N_c) :
    RGCauchyP81KernelOutput d N_c := by
  exact packet.kernelOutput

/-- Projection to the threshold-one kernel input. -/
theorem rg_cauchy_p81_kernel_input_at_one_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_packet
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (packet : BalabanRGUniformLSIQuantitativeP81ThresholdOnePacket d N_c) :
    RGCauchyP81KernelInput d N_c := by
  exact packet.kernelInput

/-- Projection to the threshold-one obligation. -/
theorem rg_cauchy_p81_obligation_at_one_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_packet
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (packet : BalabanRGUniformLSIQuantitativeP81ThresholdOnePacket d N_c) :
    RGCauchyP81Obligation d N_c := by
  exact packet.obligation

/-- Projection to the threshold-one frontier. -/
theorem rg_cauchy_p81_frontier_at_one_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_packet
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (packet : BalabanRGUniformLSIQuantitativeP81ThresholdOnePacket d N_c) :
    RGCauchyP81Frontier d N_c := by
  exact packet.frontier

/-- Projection to the threshold-one audit-link. -/
theorem balaban_rg_uniform_lsi_rg_cauchy_audit_link_at_one_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_packet
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (packet : BalabanRGUniformLSIQuantitativeP81ThresholdOnePacket d N_c) :
    BalabanRGUniformLSIRGCauchyAuditLink d N_c := by
  exact packet.auditLink

/-- Projection to the threshold-one coherence packet. -/
theorem rg_cauchy_p81_coherence_packet_at_one_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_packet
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (packet : BalabanRGUniformLSIQuantitativeP81ThresholdOnePacket d N_c) :
    RGCauchyP81CoherencePacket d N_c := by
  exact packet.coherencePacket

/-- Coherence: the explicit threshold-one increment-decay statement is canonically reconstructed
from the threshold-one bridge. -/
theorem rg_increment_decay_P81_at_one_eq_canonical_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_packet
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (packet : BalabanRGUniformLSIQuantitativeP81ThresholdOnePacket d N_c) :
    rg_increment_decay_P81_at_one_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_packet packet =
      rg_increment_decay_P81_at_one_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_bridge
        (threshold_one_bridge_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_packet packet) := by
  apply Subsingleton.elim

/-- Coherence: the explicit threshold-one summability statement is canonically reconstructed
from the threshold-one bridge. -/
theorem rg_cauchy_from_increment_decay_at_one_eq_canonical_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_packet
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (packet : BalabanRGUniformLSIQuantitativeP81ThresholdOnePacket d N_c) :
    rg_cauchy_from_increment_decay_at_one_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_packet packet =
      rg_cauchy_from_increment_decay_at_one_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_bridge
        (threshold_one_bridge_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_packet packet) := by
  apply Subsingleton.elim

/-- Coherence: the threshold-one live target is canonically reconstructed from the threshold-one
bridge. -/
theorem rg_cauchy_p81_threshold_one_live_target_eq_canonical_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_packet
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (packet : BalabanRGUniformLSIQuantitativeP81ThresholdOnePacket d N_c) :
    rg_cauchy_p81_threshold_one_live_target_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_packet packet =
      rg_cauchy_p81_threshold_one_live_target_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_bridge
        (threshold_one_bridge_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_packet packet) := by
  apply Subsingleton.elim

/-- Coherence: the threshold-one kernel output is canonically reconstructed from the threshold-one
bridge. -/
theorem rg_cauchy_p81_kernel_output_at_one_eq_canonical_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_packet
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (packet : BalabanRGUniformLSIQuantitativeP81ThresholdOnePacket d N_c) :
    rg_cauchy_p81_kernel_output_at_one_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_packet packet =
      rg_cauchy_p81_kernel_output_at_one_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_bridge
        (threshold_one_bridge_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_packet packet) := by
  apply Subsingleton.elim

/-- Coherence: the threshold-one kernel input is canonically reconstructed from the threshold-one
bridge. -/
theorem rg_cauchy_p81_kernel_input_at_one_eq_canonical_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_packet
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (packet : BalabanRGUniformLSIQuantitativeP81ThresholdOnePacket d N_c) :
    rg_cauchy_p81_kernel_input_at_one_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_packet packet =
      rg_cauchy_p81_kernel_input_at_one_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_bridge
        (threshold_one_bridge_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_packet packet) := by
  apply Subsingleton.elim

/-- Coherence: the threshold-one obligation is canonically reconstructed from the threshold-one
bridge. -/
theorem rg_cauchy_p81_obligation_at_one_eq_canonical_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_packet
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (packet : BalabanRGUniformLSIQuantitativeP81ThresholdOnePacket d N_c) :
    rg_cauchy_p81_obligation_at_one_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_packet packet =
      rg_cauchy_p81_obligation_at_one_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_bridge
        (threshold_one_bridge_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_packet packet) := by
  apply Subsingleton.elim

/-- Coherence: the threshold-one frontier is canonically reconstructed from the threshold-one
frontier bridge. -/
theorem rg_cauchy_p81_frontier_at_one_eq_canonical_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_packet
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (packet : BalabanRGUniformLSIQuantitativeP81ThresholdOnePacket d N_c) :
    rg_cauchy_p81_frontier_at_one_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_packet packet =
      rg_cauchy_p81_frontier_at_one_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_frontier_bridge
        (threshold_one_frontier_bridge_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_packet packet) := by
  apply Subsingleton.elim

/-- Coherence: the threshold-one audit-link is canonically reconstructed from the threshold-one
frontier bridge. -/
theorem balaban_rg_uniform_lsi_rg_cauchy_audit_link_at_one_eq_canonical_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_packet
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (packet : BalabanRGUniformLSIQuantitativeP81ThresholdOnePacket d N_c) :
    balaban_rg_uniform_lsi_rg_cauchy_audit_link_at_one_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_packet packet =
      balaban_rg_uniform_lsi_rg_cauchy_audit_link_at_one_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_frontier_bridge
        (threshold_one_frontier_bridge_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_packet packet) := by
  apply Subsingleton.elim

/-- Coherence: the threshold-one coherence packet is canonically reconstructed from the
threshold-one frontier bridge. -/
theorem rg_cauchy_p81_coherence_packet_at_one_eq_canonical_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_packet
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (packet : BalabanRGUniformLSIQuantitativeP81ThresholdOnePacket d N_c) :
    rg_cauchy_p81_coherence_packet_at_one_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_packet packet =
      rg_cauchy_p81_coherence_packet_at_one_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_frontier_bridge
        (threshold_one_frontier_bridge_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_packet packet) := by
  apply Subsingleton.elim

/-- Logical normal form: the threshold-one packet is equivalent to the threshold-one frontier
bridge. -/
theorem balaban_rg_uniform_lsi_quantitative_p81_threshold_one_packet_iff_threshold_one_frontier_bridge
    (d N_c : ℕ) [NeZero N_c] [∀ k, ActivityNorm d k] :
    BalabanRGUniformLSIQuantitativeP81ThresholdOnePacket d N_c ↔
      BalabanRGUniformLSIQuantitativeP81ThresholdOneFrontierBridge d N_c := by
  constructor
  · intro packet
    exact packet.thresholdOneFrontierBridge
  · intro bridge
    exact
      balaban_rg_uniform_lsi_quantitative_p81_threshold_one_packet_of_threshold_one_frontier_bridge
        d N_c bridge

/-- Logical normal form: the threshold-one packet is equivalent to the pair consisting of the
direct quantitative frontier and the theorem-side live target. -/
theorem balaban_rg_uniform_lsi_quantitative_p81_threshold_one_packet_iff_quantitative_frontier_and_live_target
    (d N_c : ℕ) [NeZero N_c] [∀ k, ActivityNorm d k] :
    BalabanRGUniformLSIQuantitativeP81ThresholdOnePacket d N_c ↔
      (BalabanRGUniformLSIQuantitativeFrontier d N_c ∧ RGCauchyP81LiveTarget d N_c) := by
  constructor
  · intro packet
    exact
      ⟨ quantitative_frontier_of_balaban_rg_uniform_lsi_quantitative_p81_kernel_packet
            (quantitative_p81_kernel_packet_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_packet
              packet),
        theorem_live_target_of_balaban_rg_uniform_lsi_quantitative_p81_kernel_packet
            (quantitative_p81_kernel_packet_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_packet
              packet) ⟩
  · intro h
    exact
      balaban_rg_uniform_lsi_quantitative_p81_threshold_one_packet_of_quantitative_frontier_and_live_target
        d N_c h.1 h.2

end

end YangMills.ClayCore
