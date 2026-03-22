import Mathlib
import YangMills.ClayCore.BalabanRG.BalabanRGUniformLSIQuantitativeAuditCoherence
import YangMills.ClayCore.BalabanRG.BalabanRGUniformLSILoadBearingPacket

namespace YangMills.ClayCore

/-- Canonical standard load-bearing packet from the quantitative Haar-LSI frontier. -/
theorem balaban_rg_uniform_lsi_load_bearing_packet_of_quantitative_frontier
    (d N_c : ℕ) [NeZero N_c]
    (frontier : BalabanRGUniformLSIQuantitativeFrontier d N_c) :
    BalabanRGUniformLSILoadBearingPacket d N_c := by
  exact
    balaban_rg_uniform_lsi_load_bearing_packet_of_activation_data d N_c
      (balaban_rg_uniform_lsi_activation_data_of_quantitative_frontier d N_c frontier)

/-- Canonical standard load-bearing packet from the quantitative audit packet. -/
theorem balaban_rg_uniform_lsi_load_bearing_packet_of_quantitative_audit_packet
    (d N_c : ℕ) [NeZero N_c]
    (packet : BalabanRGUniformLSIQuantitativeAuditPacket d N_c) :
    BalabanRGUniformLSILoadBearingPacket d N_c := by
  exact
    balaban_rg_uniform_lsi_load_bearing_packet_of_quantitative_frontier d N_c
      (quantitative_frontier_of_balaban_rg_uniform_lsi_quantitative_audit_packet packet)

/-- Canonical standard load-bearing packet from the quantitative audit coherence hub. -/
theorem balaban_rg_uniform_lsi_load_bearing_packet_of_quantitative_audit_coherence
    (d N_c : ℕ) [NeZero N_c]
    (coh : BalabanRGUniformLSIQuantitativeAuditCoherence d N_c) :
    BalabanRGUniformLSILoadBearingPacket d N_c := by
  exact
    balaban_rg_uniform_lsi_load_bearing_packet_of_quantitative_frontier d N_c
      (quantitative_frontier_of_balaban_rg_uniform_lsi_quantitative_audit_coherence coh)

/-- Canonical bridge coherence: the standard load-bearing packet reconstructed from the
quantitative frontier agrees with the one reconstructed from the public frontier it implies. -/
theorem balaban_rg_uniform_lsi_load_bearing_packet_eq_canonical_of_quantitative_frontier
    {d N_c : ℕ} [NeZero N_c]
    (frontier : BalabanRGUniformLSIQuantitativeFrontier d N_c) :
    balaban_rg_uniform_lsi_load_bearing_packet_of_quantitative_frontier d N_c frontier =
      balaban_rg_uniform_lsi_load_bearing_packet_of_frontier
        (balaban_rg_uniform_lsi_frontier_of_quantitative_frontier d N_c frontier) := by
  apply Subsingleton.elim

/-- Canonical bridge coherence: the standard load-bearing packet reconstructed from the
quantitative audit packet agrees with the one reconstructed directly from its quantitative frontier. -/
theorem balaban_rg_uniform_lsi_load_bearing_packet_eq_canonical_of_quantitative_audit_packet
    {d N_c : ℕ} [NeZero N_c]
    (packet : BalabanRGUniformLSIQuantitativeAuditPacket d N_c) :
    balaban_rg_uniform_lsi_load_bearing_packet_of_quantitative_audit_packet d N_c packet =
      balaban_rg_uniform_lsi_load_bearing_packet_of_quantitative_frontier d N_c
        (quantitative_frontier_of_balaban_rg_uniform_lsi_quantitative_audit_packet packet) := by
  apply Subsingleton.elim

/-- Canonical bridge coherence: the standard load-bearing packet reconstructed from the
quantitative audit coherence hub agrees with the one reconstructed directly from its quantitative frontier. -/
theorem balaban_rg_uniform_lsi_load_bearing_packet_eq_canonical_of_quantitative_audit_coherence
    {d N_c : ℕ} [NeZero N_c]
    (coh : BalabanRGUniformLSIQuantitativeAuditCoherence d N_c) :
    balaban_rg_uniform_lsi_load_bearing_packet_of_quantitative_audit_coherence d N_c coh =
      balaban_rg_uniform_lsi_load_bearing_packet_of_quantitative_frontier d N_c
        (quantitative_frontier_of_balaban_rg_uniform_lsi_quantitative_audit_coherence coh) := by
  apply Subsingleton.elim

/-- Projection coherence: the activation packet extracted from the bridged standard load-bearing packet
agrees canonically with the activation packet coming from the quantitative frontier. -/
theorem balaban_rg_uniform_lsi_activation_data_via_load_bearing_eq_canonical_of_quantitative_frontier
    {d N_c : ℕ} [NeZero N_c]
    (frontier : BalabanRGUniformLSIQuantitativeFrontier d N_c) :
    activation_data_of_balaban_rg_uniform_lsi_load_bearing_packet
        (balaban_rg_uniform_lsi_load_bearing_packet_of_quantitative_frontier d N_c frontier)
      =
      balaban_rg_uniform_lsi_activation_data_of_quantitative_frontier d N_c frontier := by
  apply Subsingleton.elim

/-- Projection coherence: the public frontier extracted from the bridged standard load-bearing packet
agrees canonically with the public frontier coming from the quantitative frontier. -/
theorem balaban_rg_uniform_lsi_frontier_via_load_bearing_eq_canonical_of_quantitative_frontier
    {d N_c : ℕ} [NeZero N_c]
    (frontier : BalabanRGUniformLSIQuantitativeFrontier d N_c) :
    frontier_of_balaban_rg_uniform_lsi_load_bearing_packet
        (balaban_rg_uniform_lsi_load_bearing_packet_of_quantitative_frontier d N_c frontier)
      =
      balaban_rg_uniform_lsi_frontier_of_quantitative_frontier d N_c frontier := by
  apply Subsingleton.elim

/-- Projection coherence: the frontier package extracted from the bridged standard load-bearing packet
agrees canonically with the frontier package coming from the quantitative frontier. -/
theorem balaban_rg_uniform_lsi_frontier_package_via_load_bearing_eq_canonical_of_quantitative_frontier
    {d N_c : ℕ} [NeZero N_c]
    (frontier : BalabanRGUniformLSIQuantitativeFrontier d N_c) :
    frontier_package_of_balaban_rg_uniform_lsi_load_bearing_packet
        (balaban_rg_uniform_lsi_load_bearing_packet_of_quantitative_frontier d N_c frontier)
      =
      frontier_package_of_balaban_rg_uniform_lsi_quantitative_frontier frontier := by
  apply Subsingleton.elim

/-- Projection coherence: the scale target extracted from the bridged standard load-bearing packet
agrees canonically with the scale target coming from the quantitative frontier. -/
theorem balaban_rg_uniform_lsi_scale_target_via_load_bearing_eq_canonical_of_quantitative_frontier
    {d N_c : ℕ} [NeZero N_c]
    (frontier : BalabanRGUniformLSIQuantitativeFrontier d N_c) :
    scale_target_of_balaban_rg_uniform_lsi_load_bearing_packet
        (balaban_rg_uniform_lsi_load_bearing_packet_of_quantitative_frontier d N_c frontier)
      =
      scale_target_of_balaban_rg_uniform_lsi_quantitative_frontier frontier := by
  apply Subsingleton.elim

/-- Projection coherence: the Haar target extracted from the bridged standard load-bearing packet
agrees canonically with the Haar target coming from the quantitative frontier. -/
theorem balaban_rg_uniform_lsi_haar_target_via_load_bearing_eq_canonical_of_quantitative_frontier
    {d N_c : ℕ} [NeZero N_c]
    (frontier : BalabanRGUniformLSIQuantitativeFrontier d N_c) :
    haar_target_of_balaban_rg_uniform_lsi_load_bearing_packet
        (balaban_rg_uniform_lsi_load_bearing_packet_of_quantitative_frontier d N_c frontier)
      =
      haar_target_of_balaban_rg_uniform_lsi_quantitative_frontier frontier := by
  apply Subsingleton.elim

/-- The quantitative Haar-LSI frontier already carries the same standard live target as the
standard public load-bearing lane. -/
theorem balaban_rg_uniform_lsi_live_target_of_quantitative_frontier
    (d N_c : ℕ) [NeZero N_c]
    (frontier : BalabanRGUniformLSIQuantitativeFrontier d N_c) :
    BalabanRGUniformLSILiveTarget d N_c := by
  exact
    live_target_of_balaban_rg_uniform_lsi_load_bearing_packet
      (balaban_rg_uniform_lsi_load_bearing_packet_of_quantitative_frontier d N_c frontier)

/-- The quantitative audit packet already carries the same standard live target as the
standard public load-bearing lane. -/
theorem balaban_rg_uniform_lsi_live_target_of_quantitative_audit_packet
    (d N_c : ℕ) [NeZero N_c]
    (packet : BalabanRGUniformLSIQuantitativeAuditPacket d N_c) :
    BalabanRGUniformLSILiveTarget d N_c := by
  exact
    live_target_of_balaban_rg_uniform_lsi_load_bearing_packet
      (balaban_rg_uniform_lsi_load_bearing_packet_of_quantitative_audit_packet d N_c packet)

/-- The quantitative audit coherence hub already carries the same standard live target as the
standard public load-bearing lane. -/
theorem balaban_rg_uniform_lsi_live_target_of_quantitative_audit_coherence
    (d N_c : ℕ) [NeZero N_c]
    (coh : BalabanRGUniformLSIQuantitativeAuditCoherence d N_c) :
    BalabanRGUniformLSILiveTarget d N_c := by
  exact
    live_target_of_balaban_rg_uniform_lsi_load_bearing_packet
      (balaban_rg_uniform_lsi_load_bearing_packet_of_quantitative_audit_coherence d N_c coh)

/-- The quantitative Haar-LSI frontier already carries the same standard conditional target as the
standard public load-bearing lane. -/
theorem balaban_rg_uniform_lsi_conditional_target_of_quantitative_frontier
    (d N_c : ℕ) [NeZero N_c]
    (frontier : BalabanRGUniformLSIQuantitativeFrontier d N_c) :
    BalabanRGUniformLSIConditionalTarget d N_c := by
  exact
    conditional_target_of_balaban_rg_uniform_lsi_load_bearing_packet
      (balaban_rg_uniform_lsi_load_bearing_packet_of_quantitative_frontier d N_c frontier)

/-- The quantitative audit packet already carries the same standard conditional target as the
standard public load-bearing lane. -/
theorem balaban_rg_uniform_lsi_conditional_target_of_quantitative_audit_packet
    (d N_c : ℕ) [NeZero N_c]
    (packet : BalabanRGUniformLSIQuantitativeAuditPacket d N_c) :
    BalabanRGUniformLSIConditionalTarget d N_c := by
  exact
    conditional_target_of_balaban_rg_uniform_lsi_load_bearing_packet
      (balaban_rg_uniform_lsi_load_bearing_packet_of_quantitative_audit_packet d N_c packet)

/-- The quantitative audit coherence hub already carries the same standard conditional target as the
standard public load-bearing lane. -/
theorem balaban_rg_uniform_lsi_conditional_target_of_quantitative_audit_coherence
    (d N_c : ℕ) [NeZero N_c]
    (coh : BalabanRGUniformLSIQuantitativeAuditCoherence d N_c) :
    BalabanRGUniformLSIConditionalTarget d N_c := by
  exact
    conditional_target_of_balaban_rg_uniform_lsi_load_bearing_packet
      (balaban_rg_uniform_lsi_load_bearing_packet_of_quantitative_audit_coherence d N_c coh)

end YangMills.ClayCore
