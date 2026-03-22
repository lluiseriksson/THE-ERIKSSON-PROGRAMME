import Mathlib
import YangMills.ClayCore.BalabanRG.BalabanRGUniformLSIQuantitativeP81ThresholdOneBridge

namespace YangMills.ClayCore

open scoped BigOperators
open Classical
noncomputable section

/-- Bridge from the explicit threshold-one theorem-side route to the threshold-one
`frontier` / `auditLink` / `coherencePacket` surfaces. -/
def BalabanRGUniformLSIQuantitativeP81ThresholdOneFrontierBridge
    (d N_c : ℕ) [NeZero N_c] [∀ k, ActivityNorm d k] : Prop :=
  BalabanRGUniformLSIQuantitativeP81ThresholdOneBridge d N_c

/-- Canonical bridge from the threshold-one bridge. -/
theorem balaban_rg_uniform_lsi_quantitative_p81_threshold_one_frontier_bridge_of_threshold_one_bridge
    (d N_c : ℕ) [NeZero N_c] [∀ k, ActivityNorm d k]
    (bridge : BalabanRGUniformLSIQuantitativeP81ThresholdOneBridge d N_c) :
    BalabanRGUniformLSIQuantitativeP81ThresholdOneFrontierBridge d N_c := by
  exact bridge

/-- Canonical bridge from the direct quantitative frontier together with the theorem-side live
target. -/
theorem balaban_rg_uniform_lsi_quantitative_p81_threshold_one_frontier_bridge_of_quantitative_frontier_and_live_target
    (d N_c : ℕ) [NeZero N_c] [∀ k, ActivityNorm d k]
    (frontier : BalabanRGUniformLSIQuantitativeFrontier d N_c)
    (live : RGCauchyP81LiveTarget d N_c) :
    BalabanRGUniformLSIQuantitativeP81ThresholdOneFrontierBridge d N_c := by
  exact
    balaban_rg_uniform_lsi_quantitative_p81_threshold_one_bridge_of_quantitative_frontier_and_live_target
      d N_c frontier live

/-- Projection back to the threshold-one bridge. -/
theorem threshold_one_bridge_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_frontier_bridge
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (bridge : BalabanRGUniformLSIQuantitativeP81ThresholdOneFrontierBridge d N_c) :
    BalabanRGUniformLSIQuantitativeP81ThresholdOneBridge d N_c := by
  exact bridge

/-- Projection back to the quantitative P81 kernel packet. -/
theorem quantitative_p81_kernel_packet_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_frontier_bridge
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (bridge : BalabanRGUniformLSIQuantitativeP81ThresholdOneFrontierBridge d N_c) :
    BalabanRGUniformLSIQuantitativeP81KernelPacket d N_c := by
  exact
    quantitative_p81_kernel_packet_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_bridge
      (threshold_one_bridge_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_frontier_bridge bridge)

/-- Standard audit packet attached to the quantitative threshold-one route. -/
theorem standard_audit_packet_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_frontier_bridge
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (bridge : BalabanRGUniformLSIQuantitativeP81ThresholdOneFrontierBridge d N_c) :
    BalabanRGUniformLSIAuditPacket d N_c := by
  exact
    standard_audit_packet_of_balaban_rg_uniform_lsi_quantitative_p81_obstruction_coherence
      (quantitative_p81_obstruction_coherence_of_balaban_rg_uniform_lsi_quantitative_p81_kernel_packet
        (quantitative_p81_kernel_packet_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_frontier_bridge
          bridge))

/-- Explicit threshold-one frontier reconstructed from the threshold-one theorem-side live target
and the standard audit packet attached to the quantitative route. -/
theorem rg_cauchy_p81_frontier_at_one_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_frontier_bridge
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (bridge : BalabanRGUniformLSIQuantitativeP81ThresholdOneFrontierBridge d N_c) :
    RGCauchyP81Frontier d N_c := by
  exact
    rg_cauchy_p81_frontier_of_audit_packet_and_live_target d N_c
      (standard_audit_packet_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_frontier_bridge bridge)
      (rg_cauchy_p81_threshold_one_live_target_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_bridge
        (threshold_one_bridge_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_frontier_bridge bridge))

/-- Explicit threshold-one audit-link surface reconstructed from the threshold-one theorem-side
live target and the standard audit packet attached to the quantitative route. -/
theorem balaban_rg_uniform_lsi_rg_cauchy_audit_link_at_one_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_frontier_bridge
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (bridge : BalabanRGUniformLSIQuantitativeP81ThresholdOneFrontierBridge d N_c) :
    BalabanRGUniformLSIRGCauchyAuditLink d N_c := by
  exact
    balaban_rg_uniform_lsi_rg_cauchy_audit_link_of_audit_packet_and_live_target d N_c
      (standard_audit_packet_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_frontier_bridge bridge)
      (rg_cauchy_p81_threshold_one_live_target_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_bridge
        (threshold_one_bridge_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_frontier_bridge bridge))

/-- Explicit threshold-one coherence packet reconstructed from the threshold-one theorem-side
live target and the standard audit packet attached to the quantitative route. -/
theorem rg_cauchy_p81_coherence_packet_at_one_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_frontier_bridge
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (bridge : BalabanRGUniformLSIQuantitativeP81ThresholdOneFrontierBridge d N_c) :
    RGCauchyP81CoherencePacket d N_c := by
  exact
    rg_cauchy_p81_coherence_packet_of_audit_packet_and_live_target d N_c
      (standard_audit_packet_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_frontier_bridge bridge)
      (rg_cauchy_p81_threshold_one_live_target_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_bridge
        (threshold_one_bridge_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_frontier_bridge bridge))

/-- Bridge coherence: the frontier carried by the quantitative kernel packet agrees canonically
with the explicit threshold-one frontier. -/
theorem rg_cauchy_p81_frontier_at_one_eq_canonical_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_frontier_bridge
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (bridge : BalabanRGUniformLSIQuantitativeP81ThresholdOneFrontierBridge d N_c) :
    rg_cauchy_p81_frontier_of_balaban_rg_uniform_lsi_quantitative_p81_kernel_packet
        (quantitative_p81_kernel_packet_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_frontier_bridge
          bridge)
      =
      rg_cauchy_p81_frontier_at_one_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_frontier_bridge
        bridge := by
  apply Subsingleton.elim

/-- Bridge coherence: the audit-link carried by the quantitative kernel packet via its theorem-side
coherence packet agrees canonically with the explicit threshold-one audit-link. -/
theorem balaban_rg_uniform_lsi_rg_cauchy_audit_link_at_one_eq_canonical_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_frontier_bridge
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (bridge : BalabanRGUniformLSIQuantitativeP81ThresholdOneFrontierBridge d N_c) :
    balaban_rg_uniform_lsi_rg_cauchy_audit_link_of_coherence_packet
        (rg_cauchy_p81_coherence_packet_of_balaban_rg_uniform_lsi_quantitative_p81_kernel_packet
          (quantitative_p81_kernel_packet_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_frontier_bridge
            bridge))
      =
      balaban_rg_uniform_lsi_rg_cauchy_audit_link_at_one_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_frontier_bridge
        bridge := by
  apply Subsingleton.elim

/-- Bridge coherence: the coherence packet carried by the quantitative kernel packet agrees
canonically with the explicit threshold-one coherence packet. -/
theorem rg_cauchy_p81_coherence_packet_at_one_eq_canonical_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_frontier_bridge
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (bridge : BalabanRGUniformLSIQuantitativeP81ThresholdOneFrontierBridge d N_c) :
    rg_cauchy_p81_coherence_packet_of_balaban_rg_uniform_lsi_quantitative_p81_kernel_packet
        (quantitative_p81_kernel_packet_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_frontier_bridge
          bridge)
      =
      rg_cauchy_p81_coherence_packet_at_one_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_frontier_bridge
        bridge := by
  apply Subsingleton.elim

/-- Logical normal form: the threshold-one frontier bridge is equivalent to the threshold-one
bridge. -/
theorem balaban_rg_uniform_lsi_quantitative_p81_threshold_one_frontier_bridge_iff_threshold_one_bridge
    (d N_c : ℕ) [NeZero N_c] [∀ k, ActivityNorm d k] :
    BalabanRGUniformLSIQuantitativeP81ThresholdOneFrontierBridge d N_c ↔
      BalabanRGUniformLSIQuantitativeP81ThresholdOneBridge d N_c := by
  constructor
  · intro bridge
    exact bridge
  · intro bridge
    exact bridge

/-- Logical normal form: the threshold-one frontier bridge is equivalent to the pair consisting
of the direct quantitative frontier and the theorem-side live target. -/
theorem balaban_rg_uniform_lsi_quantitative_p81_threshold_one_frontier_bridge_iff_quantitative_frontier_and_live_target
    (d N_c : ℕ) [NeZero N_c] [∀ k, ActivityNorm d k] :
    BalabanRGUniformLSIQuantitativeP81ThresholdOneFrontierBridge d N_c ↔
      (BalabanRGUniformLSIQuantitativeFrontier d N_c ∧ RGCauchyP81LiveTarget d N_c) := by
  constructor
  · intro bridge
    exact
      ⟨ quantitative_frontier_of_balaban_rg_uniform_lsi_quantitative_p81_kernel_packet
            (quantitative_p81_kernel_packet_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_frontier_bridge
              bridge),
        theorem_live_target_of_balaban_rg_uniform_lsi_quantitative_p81_kernel_packet
            (quantitative_p81_kernel_packet_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_frontier_bridge
              bridge) ⟩
  · intro h
    exact
      balaban_rg_uniform_lsi_quantitative_p81_threshold_one_frontier_bridge_of_quantitative_frontier_and_live_target
        d N_c h.1 h.2

end

end YangMills.ClayCore
