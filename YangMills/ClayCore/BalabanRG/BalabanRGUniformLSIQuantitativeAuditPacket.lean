import Mathlib
import YangMills.ClayCore.BalabanRG.BalabanRGUniformLSIQuantitativeFrontier

namespace YangMills.ClayCore

/-- Unified audit-style packet for the direct quantitative Balaban-RG / Haar-LSI route. -/
structure BalabanRGUniformLSIQuantitativeAuditPacket
    (d N_c : ℕ) [NeZero N_c] : Prop where
  quantitativeFrontier : BalabanRGUniformLSIQuantitativeFrontier d N_c
  activationData : BalabanRGUniformLSIActivationData d N_c
  laneContract : BalabanRGUniformLSILaneContract d N_c
  frontier : BalabanRGUniformLSIFrontier d N_c
  publicFacade : BalabanRGUniformLSIPublicFacade d N_c
  closurePackage : BalabanRGUniformLSIClosurePackage d N_c
  equivalenceRegistry : BalabanRGUniformLSIEquivalenceRegistry d N_c
  scaleTarget : SpecialUnitaryScaleLSITarget d N_c
  haarTarget : HaarLSITarget N_c
  frontierPackage : HaarLSIFrontierPackage d N_c

/-- Canonical audit packet from the quantitative Haar-LSI frontier. -/
theorem balaban_rg_uniform_lsi_quantitative_audit_packet_of_quantitative_frontier
    (d N_c : ℕ) [NeZero N_c]
    (frontier : BalabanRGUniformLSIQuantitativeFrontier d N_c) :
    BalabanRGUniformLSIQuantitativeAuditPacket d N_c := by
  exact
    ⟨ frontier,
      balaban_rg_uniform_lsi_activation_data_of_quantitative_frontier d N_c frontier,
      balaban_rg_uniform_lsi_lane_contract_of_quantitative_frontier d N_c frontier,
      balaban_rg_uniform_lsi_frontier_of_quantitative_frontier d N_c frontier,
      balaban_rg_uniform_lsi_public_facade_of_quantitative_frontier d N_c frontier,
      balaban_rg_uniform_lsi_closure_package_of_quantitative_frontier d N_c frontier,
      balaban_rg_uniform_lsi_equivalence_registry_of_quantitative_frontier d N_c frontier,
      scale_target_of_balaban_rg_uniform_lsi_quantitative_frontier frontier,
      haar_target_of_balaban_rg_uniform_lsi_quantitative_frontier frontier,
      frontier_package_of_balaban_rg_uniform_lsi_quantitative_frontier frontier ⟩

/-- Projection to the quantitative Haar-LSI frontier. -/
theorem quantitative_frontier_of_balaban_rg_uniform_lsi_quantitative_audit_packet
    {d N_c : ℕ} [NeZero N_c]
    (packet : BalabanRGUniformLSIQuantitativeAuditPacket d N_c) :
    BalabanRGUniformLSIQuantitativeFrontier d N_c := by
  exact packet.quantitativeFrontier

/-- Projection to the transfer ingredient. -/
theorem transfer_of_balaban_rg_uniform_lsi_quantitative_audit_packet
    {d N_c : ℕ} [NeZero N_c]
    (packet : BalabanRGUniformLSIQuantitativeAuditPacket d N_c) :
    HaarLSIFromUniformLSITransfer N_c := by
  exact packet.quantitativeFrontier.transfer

/-- Projection to the quantitative rates frontier. -/
theorem physical_rg_rates_frontier_of_balaban_rg_uniform_lsi_quantitative_audit_packet
    {d N_c : ℕ} [NeZero N_c]
    (packet : BalabanRGUniformLSIQuantitativeAuditPacket d N_c) :
    PhysicalRGRatesFrontier d N_c := by
  exact packet.quantitativeFrontier.ratesFrontier

/-- Projection to the package-side witness. -/
theorem balaban_rg_package_of_quantitative_audit_packet
    {d N_c : ℕ} [NeZero N_c]
    (packet : BalabanRGUniformLSIQuantitativeAuditPacket d N_c) :
    BalabanRGPackage d N_c := by
  exact
    balaban_rg_package_of_balaban_rg_uniform_lsi_quantitative_frontier
      packet.quantitativeFrontier

/-- Projection to the canonical activation data. -/
theorem balaban_rg_uniform_lsi_activation_data_of_quantitative_audit_packet
    {d N_c : ℕ} [NeZero N_c]
    (packet : BalabanRGUniformLSIQuantitativeAuditPacket d N_c) :
    BalabanRGUniformLSIActivationData d N_c := by
  exact packet.activationData

/-- Projection to the preferred short public frontier. -/
theorem balaban_rg_uniform_lsi_frontier_of_quantitative_audit_packet
    {d N_c : ℕ} [NeZero N_c]
    (packet : BalabanRGUniformLSIQuantitativeAuditPacket d N_c) :
    BalabanRGUniformLSIFrontier d N_c := by
  exact packet.frontier

/-- Projection to the preferred public facade. -/
theorem balaban_rg_uniform_lsi_public_facade_of_quantitative_audit_packet
    {d N_c : ℕ} [NeZero N_c]
    (packet : BalabanRGUniformLSIQuantitativeAuditPacket d N_c) :
    BalabanRGUniformLSIPublicFacade d N_c := by
  exact packet.publicFacade

/-- Projection to the scale target. -/
theorem scale_target_of_balaban_rg_uniform_lsi_quantitative_audit_packet
    {d N_c : ℕ} [NeZero N_c]
    (packet : BalabanRGUniformLSIQuantitativeAuditPacket d N_c) :
    SpecialUnitaryScaleLSITarget d N_c := by
  exact packet.scaleTarget

/-- Projection to the Haar target. -/
theorem haar_target_of_balaban_rg_uniform_lsi_quantitative_audit_packet
    {d N_c : ℕ} [NeZero N_c]
    (packet : BalabanRGUniformLSIQuantitativeAuditPacket d N_c) :
    HaarLSITarget N_c := by
  exact packet.haarTarget

/-- Projection to the frontier package. -/
theorem frontier_package_of_balaban_rg_uniform_lsi_quantitative_audit_packet
    {d N_c : ℕ} [NeZero N_c]
    (packet : BalabanRGUniformLSIQuantitativeAuditPacket d N_c) :
    HaarLSIFrontierPackage d N_c := by
  exact packet.frontierPackage

/-- Logical normal form: the quantitative audit packet is equivalent to the quantitative Haar-LSI frontier. -/
theorem balaban_rg_uniform_lsi_quantitative_audit_packet_iff_quantitative_frontier
    (d N_c : ℕ) [NeZero N_c] :
    BalabanRGUniformLSIQuantitativeAuditPacket d N_c ↔
      BalabanRGUniformLSIQuantitativeFrontier d N_c := by
  constructor
  · intro packet
    exact packet.quantitativeFrontier
  · intro frontier
    exact balaban_rg_uniform_lsi_quantitative_audit_packet_of_quantitative_frontier d N_c frontier

/-- Logical normal form: the quantitative audit packet is equivalent to the pair
consisting of the transfer ingredient and the quantitative rates frontier. -/
theorem balaban_rg_uniform_lsi_quantitative_audit_packet_iff_pair
    (d N_c : ℕ) [NeZero N_c] :
    BalabanRGUniformLSIQuantitativeAuditPacket d N_c ↔
      (HaarLSIFromUniformLSITransfer N_c ∧ PhysicalRGRatesFrontier d N_c) := by
  constructor
  · intro packet
    exact
      (balaban_rg_uniform_lsi_quantitative_frontier_iff_pair d N_c).1
        packet.quantitativeFrontier
  · intro h
    exact
      balaban_rg_uniform_lsi_quantitative_audit_packet_of_quantitative_frontier d N_c
        ((balaban_rg_uniform_lsi_quantitative_frontier_iff_pair d N_c).2 h)

/-- Coherence: the quantitative audit packet is propositionally equal to the canonical one
reconstructed from its quantitative frontier. -/
theorem balaban_rg_uniform_lsi_quantitative_audit_packet_eq_canonical_of_quantitative_frontier
    {d N_c : ℕ} [NeZero N_c]
    (packet : BalabanRGUniformLSIQuantitativeAuditPacket d N_c) :
    packet =
      balaban_rg_uniform_lsi_quantitative_audit_packet_of_quantitative_frontier d N_c
        packet.quantitativeFrontier := by
  apply Subsingleton.elim

end YangMills.ClayCore
