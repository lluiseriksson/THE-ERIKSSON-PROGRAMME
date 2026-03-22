import Mathlib
import YangMills.ClayCore.BalabanRG.BalabanRGUniformLSIQuantitativeLoadBearingBridge

namespace YangMills.ClayCore

/-- Unified load-bearing packet for the direct quantitative Balaban-RG / Haar-LSI route. -/
structure BalabanRGUniformLSIQuantitativeLoadBearingPacket
    (d N_c : ℕ) [NeZero N_c] : Prop where
  quantitativeFrontier : BalabanRGUniformLSIQuantitativeFrontier d N_c
  loadBearingPacket : BalabanRGUniformLSILoadBearingPacket d N_c
  ratesFrontier : PhysicalRGRatesFrontier d N_c
  activationData : BalabanRGUniformLSIActivationData d N_c
  publicFrontier : BalabanRGUniformLSIFrontier d N_c
  publicFacade : BalabanRGUniformLSIPublicFacade d N_c
  liveTarget : BalabanRGUniformLSILiveTarget d N_c
  conditionalTarget : BalabanRGUniformLSIConditionalTarget d N_c
  scaleTarget : SpecialUnitaryScaleLSITarget d N_c
  haarTarget : HaarLSITarget N_c
  frontierPackage : HaarLSIFrontierPackage d N_c

/-- Canonical quantitative load-bearing packet from the quantitative Haar-LSI frontier. -/
theorem balaban_rg_uniform_lsi_quantitative_load_bearing_packet_of_quantitative_frontier
    (d N_c : ℕ) [NeZero N_c]
    (frontier : BalabanRGUniformLSIQuantitativeFrontier d N_c) :
    BalabanRGUniformLSIQuantitativeLoadBearingPacket d N_c := by
  exact
    ⟨ frontier,
      balaban_rg_uniform_lsi_load_bearing_packet_of_quantitative_frontier d N_c frontier,
      physical_rg_rates_frontier_of_balaban_rg_uniform_lsi_quantitative_frontier frontier,
      balaban_rg_uniform_lsi_activation_data_of_quantitative_frontier d N_c frontier,
      balaban_rg_uniform_lsi_frontier_of_quantitative_frontier d N_c frontier,
      balaban_rg_uniform_lsi_public_facade_of_quantitative_frontier d N_c frontier,
      balaban_rg_uniform_lsi_live_target_of_quantitative_frontier d N_c frontier,
      balaban_rg_uniform_lsi_conditional_target_of_quantitative_frontier d N_c frontier,
      scale_target_of_balaban_rg_uniform_lsi_quantitative_frontier frontier,
      haar_target_of_balaban_rg_uniform_lsi_quantitative_frontier frontier,
      frontier_package_of_balaban_rg_uniform_lsi_quantitative_frontier frontier ⟩

/-- Canonical quantitative load-bearing packet from the quantitative audit packet. -/
theorem balaban_rg_uniform_lsi_quantitative_load_bearing_packet_of_quantitative_audit_packet
    (d N_c : ℕ) [NeZero N_c]
    (packet : BalabanRGUniformLSIQuantitativeAuditPacket d N_c) :
    BalabanRGUniformLSIQuantitativeLoadBearingPacket d N_c := by
  exact
    balaban_rg_uniform_lsi_quantitative_load_bearing_packet_of_quantitative_frontier d N_c
      (quantitative_frontier_of_balaban_rg_uniform_lsi_quantitative_audit_packet packet)

/-- Canonical quantitative load-bearing packet from the quantitative audit coherence hub. -/
theorem balaban_rg_uniform_lsi_quantitative_load_bearing_packet_of_quantitative_audit_coherence
    (d N_c : ℕ) [NeZero N_c]
    (coh : BalabanRGUniformLSIQuantitativeAuditCoherence d N_c) :
    BalabanRGUniformLSIQuantitativeLoadBearingPacket d N_c := by
  exact
    balaban_rg_uniform_lsi_quantitative_load_bearing_packet_of_quantitative_frontier d N_c
      (quantitative_frontier_of_balaban_rg_uniform_lsi_quantitative_audit_coherence coh)

/-- Projection to the quantitative Haar-LSI frontier. -/
theorem quantitative_frontier_of_balaban_rg_uniform_lsi_quantitative_load_bearing_packet
    {d N_c : ℕ} [NeZero N_c]
    (packet : BalabanRGUniformLSIQuantitativeLoadBearingPacket d N_c) :
    BalabanRGUniformLSIQuantitativeFrontier d N_c := by
  exact packet.quantitativeFrontier

/-- Projection to the transfer ingredient. -/
theorem transfer_of_balaban_rg_uniform_lsi_quantitative_load_bearing_packet
    {d N_c : ℕ} [NeZero N_c]
    (packet : BalabanRGUniformLSIQuantitativeLoadBearingPacket d N_c) :
    HaarLSIFromUniformLSITransfer N_c := by
  exact packet.quantitativeFrontier.transfer

/-- Projection to the quantitative rates frontier. -/
theorem rates_frontier_of_balaban_rg_uniform_lsi_quantitative_load_bearing_packet
    {d N_c : ℕ} [NeZero N_c]
    (packet : BalabanRGUniformLSIQuantitativeLoadBearingPacket d N_c) :
    PhysicalRGRatesFrontier d N_c := by
  exact packet.ratesFrontier

/-- Projection to the standard load-bearing landing surface. -/
theorem load_bearing_packet_of_balaban_rg_uniform_lsi_quantitative_load_bearing_packet
    {d N_c : ℕ} [NeZero N_c]
    (packet : BalabanRGUniformLSIQuantitativeLoadBearingPacket d N_c) :
    BalabanRGUniformLSILoadBearingPacket d N_c := by
  exact packet.loadBearingPacket

/-- Projection to the canonical activation data. -/
theorem activation_data_of_balaban_rg_uniform_lsi_quantitative_load_bearing_packet
    {d N_c : ℕ} [NeZero N_c]
    (packet : BalabanRGUniformLSIQuantitativeLoadBearingPacket d N_c) :
    BalabanRGUniformLSIActivationData d N_c := by
  exact packet.activationData

/-- Projection to the preferred short public frontier. -/
theorem public_frontier_of_balaban_rg_uniform_lsi_quantitative_load_bearing_packet
    {d N_c : ℕ} [NeZero N_c]
    (packet : BalabanRGUniformLSIQuantitativeLoadBearingPacket d N_c) :
    BalabanRGUniformLSIFrontier d N_c := by
  exact packet.publicFrontier

/-- Projection to the preferred public facade. -/
theorem public_facade_of_balaban_rg_uniform_lsi_quantitative_load_bearing_packet
    {d N_c : ℕ} [NeZero N_c]
    (packet : BalabanRGUniformLSIQuantitativeLoadBearingPacket d N_c) :
    BalabanRGUniformLSIPublicFacade d N_c := by
  exact packet.publicFacade

/-- Projection to the preferred live target. -/
theorem live_target_of_balaban_rg_uniform_lsi_quantitative_load_bearing_packet
    {d N_c : ℕ} [NeZero N_c]
    (packet : BalabanRGUniformLSIQuantitativeLoadBearingPacket d N_c) :
    BalabanRGUniformLSILiveTarget d N_c := by
  exact packet.liveTarget

/-- Projection to the conditional target. -/
theorem conditional_target_of_balaban_rg_uniform_lsi_quantitative_load_bearing_packet
    {d N_c : ℕ} [NeZero N_c]
    (packet : BalabanRGUniformLSIQuantitativeLoadBearingPacket d N_c) :
    BalabanRGUniformLSIConditionalTarget d N_c := by
  exact packet.conditionalTarget

/-- Projection to the scale target. -/
theorem scale_target_of_balaban_rg_uniform_lsi_quantitative_load_bearing_packet
    {d N_c : ℕ} [NeZero N_c]
    (packet : BalabanRGUniformLSIQuantitativeLoadBearingPacket d N_c) :
    SpecialUnitaryScaleLSITarget d N_c := by
  exact packet.scaleTarget

/-- Projection to the Haar target. -/
theorem haar_target_of_balaban_rg_uniform_lsi_quantitative_load_bearing_packet
    {d N_c : ℕ} [NeZero N_c]
    (packet : BalabanRGUniformLSIQuantitativeLoadBearingPacket d N_c) :
    HaarLSITarget N_c := by
  exact packet.haarTarget

/-- Projection to the frontier package. -/
theorem frontier_package_of_balaban_rg_uniform_lsi_quantitative_load_bearing_packet
    {d N_c : ℕ} [NeZero N_c]
    (packet : BalabanRGUniformLSIQuantitativeLoadBearingPacket d N_c) :
    HaarLSIFrontierPackage d N_c := by
  exact packet.frontierPackage

/-- Logical normal form: the quantitative load-bearing packet is equivalent to the
quantitative Haar-LSI frontier. -/
theorem balaban_rg_uniform_lsi_quantitative_load_bearing_packet_iff_quantitative_frontier
    (d N_c : ℕ) [NeZero N_c] :
    BalabanRGUniformLSIQuantitativeLoadBearingPacket d N_c ↔
      BalabanRGUniformLSIQuantitativeFrontier d N_c := by
  constructor
  · intro packet
    exact packet.quantitativeFrontier
  · intro frontier
    exact
      balaban_rg_uniform_lsi_quantitative_load_bearing_packet_of_quantitative_frontier
        d N_c frontier

/-- Logical normal form: the quantitative load-bearing packet is equivalent to the
quantitative audit packet. -/
theorem balaban_rg_uniform_lsi_quantitative_load_bearing_packet_iff_quantitative_audit_packet
    (d N_c : ℕ) [NeZero N_c] :
    BalabanRGUniformLSIQuantitativeLoadBearingPacket d N_c ↔
      BalabanRGUniformLSIQuantitativeAuditPacket d N_c := by
  constructor
  · intro packet
    exact
      balaban_rg_uniform_lsi_quantitative_audit_packet_of_quantitative_frontier d N_c
        (quantitative_frontier_of_balaban_rg_uniform_lsi_quantitative_load_bearing_packet packet)
  · intro audit
    exact
      balaban_rg_uniform_lsi_quantitative_load_bearing_packet_of_quantitative_audit_packet
        d N_c audit

/-- Logical normal form: the quantitative load-bearing packet is equivalent to the
quantitative audit coherence hub. -/
theorem balaban_rg_uniform_lsi_quantitative_load_bearing_packet_iff_quantitative_audit_coherence
    (d N_c : ℕ) [NeZero N_c] :
    BalabanRGUniformLSIQuantitativeLoadBearingPacket d N_c ↔
      BalabanRGUniformLSIQuantitativeAuditCoherence d N_c := by
  constructor
  · intro packet
    exact
      balaban_rg_uniform_lsi_quantitative_audit_coherence_of_quantitative_frontier d N_c
        (quantitative_frontier_of_balaban_rg_uniform_lsi_quantitative_load_bearing_packet packet)
  · intro coh
    exact
      balaban_rg_uniform_lsi_quantitative_load_bearing_packet_of_quantitative_audit_coherence
        d N_c coh

/-- Logical normal form: the quantitative load-bearing packet is equivalent to the pair
consisting of the transfer ingredient and the quantitative rates frontier. -/
theorem balaban_rg_uniform_lsi_quantitative_load_bearing_packet_iff_pair
    (d N_c : ℕ) [NeZero N_c] :
    BalabanRGUniformLSIQuantitativeLoadBearingPacket d N_c ↔
      (HaarLSIFromUniformLSITransfer N_c ∧ PhysicalRGRatesFrontier d N_c) := by
  constructor
  · intro packet
    exact
      (balaban_rg_uniform_lsi_quantitative_frontier_iff_pair d N_c).1
        (quantitative_frontier_of_balaban_rg_uniform_lsi_quantitative_load_bearing_packet packet)
  · intro h
    exact
      balaban_rg_uniform_lsi_quantitative_load_bearing_packet_of_quantitative_frontier d N_c
        ((balaban_rg_uniform_lsi_quantitative_frontier_iff_pair d N_c).2 h)

/-- Coherence: the quantitative load-bearing packet is propositionally equal to the canonical
one reconstructed from its quantitative frontier. -/
theorem balaban_rg_uniform_lsi_quantitative_load_bearing_packet_eq_canonical_of_quantitative_frontier
    {d N_c : ℕ} [NeZero N_c]
    (packet : BalabanRGUniformLSIQuantitativeLoadBearingPacket d N_c) :
    packet =
      balaban_rg_uniform_lsi_quantitative_load_bearing_packet_of_quantitative_frontier d N_c
        (quantitative_frontier_of_balaban_rg_uniform_lsi_quantitative_load_bearing_packet packet) := by
  apply Subsingleton.elim

/-- Coherence: the quantitative load-bearing packet reconstructed from a quantitative audit
packet agrees canonically with the one reconstructed from its quantitative frontier. -/
theorem balaban_rg_uniform_lsi_quantitative_load_bearing_packet_eq_canonical_of_quantitative_audit_packet
    {d N_c : ℕ} [NeZero N_c]
    (packet : BalabanRGUniformLSIQuantitativeAuditPacket d N_c) :
    balaban_rg_uniform_lsi_quantitative_load_bearing_packet_of_quantitative_audit_packet d N_c packet
      =
      balaban_rg_uniform_lsi_quantitative_load_bearing_packet_of_quantitative_frontier d N_c
        (quantitative_frontier_of_balaban_rg_uniform_lsi_quantitative_audit_packet packet) := by
  apply Subsingleton.elim

/-- Coherence: the quantitative load-bearing packet reconstructed from a quantitative audit
coherence hub agrees canonically with the one reconstructed from its quantitative frontier. -/
theorem balaban_rg_uniform_lsi_quantitative_load_bearing_packet_eq_canonical_of_quantitative_audit_coherence
    {d N_c : ℕ} [NeZero N_c]
    (coh : BalabanRGUniformLSIQuantitativeAuditCoherence d N_c) :
    balaban_rg_uniform_lsi_quantitative_load_bearing_packet_of_quantitative_audit_coherence d N_c coh
      =
      balaban_rg_uniform_lsi_quantitative_load_bearing_packet_of_quantitative_frontier d N_c
        (quantitative_frontier_of_balaban_rg_uniform_lsi_quantitative_audit_coherence coh) := by
  apply Subsingleton.elim

end YangMills.ClayCore
