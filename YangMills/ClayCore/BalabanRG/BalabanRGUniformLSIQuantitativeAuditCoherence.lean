import Mathlib
import YangMills.ClayCore.BalabanRG.BalabanRGUniformLSIQuantitativeAuditPacket

namespace YangMills.ClayCore

/-- Coherence hub for the direct quantitative Balaban-RG / Haar-LSI public surface. -/
structure BalabanRGUniformLSIQuantitativeAuditCoherence
    (d N_c : ℕ) [NeZero N_c] : Prop where
  auditPacket : BalabanRGUniformLSIQuantitativeAuditPacket d N_c
  quantitativeFrontier : BalabanRGUniformLSIQuantitativeFrontier d N_c
  ratesFrontier : PhysicalRGRatesFrontier d N_c
  publicFrontier : BalabanRGUniformLSIFrontier d N_c
  publicFacade : BalabanRGUniformLSIPublicFacade d N_c

/-- Canonical coherence hub from the quantitative Haar-LSI frontier. -/
theorem balaban_rg_uniform_lsi_quantitative_audit_coherence_of_quantitative_frontier
    (d N_c : ℕ) [NeZero N_c]
    (frontier : BalabanRGUniformLSIQuantitativeFrontier d N_c) :
    BalabanRGUniformLSIQuantitativeAuditCoherence d N_c := by
  exact
    ⟨ balaban_rg_uniform_lsi_quantitative_audit_packet_of_quantitative_frontier d N_c frontier,
      frontier,
      physical_rg_rates_frontier_of_balaban_rg_uniform_lsi_quantitative_frontier frontier,
      balaban_rg_uniform_lsi_frontier_of_quantitative_frontier d N_c frontier,
      balaban_rg_uniform_lsi_public_facade_of_quantitative_frontier d N_c frontier ⟩

/-- Canonical coherence hub from the quantitative audit packet. -/
theorem balaban_rg_uniform_lsi_quantitative_audit_coherence_of_quantitative_audit_packet
    (d N_c : ℕ) [NeZero N_c]
    (packet : BalabanRGUniformLSIQuantitativeAuditPacket d N_c) :
    BalabanRGUniformLSIQuantitativeAuditCoherence d N_c := by
  exact
    balaban_rg_uniform_lsi_quantitative_audit_coherence_of_quantitative_frontier d N_c
      (quantitative_frontier_of_balaban_rg_uniform_lsi_quantitative_audit_packet packet)

/-- Projection to the quantitative audit packet. -/
theorem quantitative_audit_packet_of_balaban_rg_uniform_lsi_quantitative_audit_coherence
    {d N_c : ℕ} [NeZero N_c]
    (coh : BalabanRGUniformLSIQuantitativeAuditCoherence d N_c) :
    BalabanRGUniformLSIQuantitativeAuditPacket d N_c := by
  exact coh.auditPacket

/-- Projection to the quantitative Haar-LSI frontier. -/
theorem quantitative_frontier_of_balaban_rg_uniform_lsi_quantitative_audit_coherence
    {d N_c : ℕ} [NeZero N_c]
    (coh : BalabanRGUniformLSIQuantitativeAuditCoherence d N_c) :
    BalabanRGUniformLSIQuantitativeFrontier d N_c := by
  exact coh.quantitativeFrontier

/-- Projection to the quantitative rates frontier. -/
theorem rates_frontier_of_balaban_rg_uniform_lsi_quantitative_audit_coherence
    {d N_c : ℕ} [NeZero N_c]
    (coh : BalabanRGUniformLSIQuantitativeAuditCoherence d N_c) :
    PhysicalRGRatesFrontier d N_c := by
  exact coh.ratesFrontier

/-- Projection to the public Haar-LSI frontier. -/
theorem public_frontier_of_balaban_rg_uniform_lsi_quantitative_audit_coherence
    {d N_c : ℕ} [NeZero N_c]
    (coh : BalabanRGUniformLSIQuantitativeAuditCoherence d N_c) :
    BalabanRGUniformLSIFrontier d N_c := by
  exact coh.publicFrontier

/-- Projection to the public facade. -/
theorem public_facade_of_balaban_rg_uniform_lsi_quantitative_audit_coherence
    {d N_c : ℕ} [NeZero N_c]
    (coh : BalabanRGUniformLSIQuantitativeAuditCoherence d N_c) :
    BalabanRGUniformLSIPublicFacade d N_c := by
  exact coh.publicFacade

/-- Logical normal form: the quantitative coherence hub is equivalent to the quantitative frontier. -/
theorem balaban_rg_uniform_lsi_quantitative_audit_coherence_iff_quantitative_frontier
    (d N_c : ℕ) [NeZero N_c] :
    BalabanRGUniformLSIQuantitativeAuditCoherence d N_c ↔
      BalabanRGUniformLSIQuantitativeFrontier d N_c := by
  constructor
  · intro coh
    exact coh.quantitativeFrontier
  · intro frontier
    exact
      balaban_rg_uniform_lsi_quantitative_audit_coherence_of_quantitative_frontier d N_c
        frontier

/-- Logical normal form: the quantitative coherence hub is equivalent to the quantitative audit packet. -/
theorem balaban_rg_uniform_lsi_quantitative_audit_coherence_iff_quantitative_audit_packet
    (d N_c : ℕ) [NeZero N_c] :
    BalabanRGUniformLSIQuantitativeAuditCoherence d N_c ↔
      BalabanRGUniformLSIQuantitativeAuditPacket d N_c := by
  constructor
  · intro coh
    exact coh.auditPacket
  · intro packet
    exact
      balaban_rg_uniform_lsi_quantitative_audit_coherence_of_quantitative_audit_packet d N_c
        packet

/-- Logical normal form: the quantitative coherence hub is equivalent to the pair
consisting of the transfer ingredient and the quantitative rates frontier. -/
theorem balaban_rg_uniform_lsi_quantitative_audit_coherence_iff_pair
    (d N_c : ℕ) [NeZero N_c] :
    BalabanRGUniformLSIQuantitativeAuditCoherence d N_c ↔
      (HaarLSIFromUniformLSITransfer N_c ∧ PhysicalRGRatesFrontier d N_c) := by
  constructor
  · intro coh
    exact
      (balaban_rg_uniform_lsi_quantitative_frontier_iff_pair d N_c).1
        coh.quantitativeFrontier
  · intro h
    exact
      balaban_rg_uniform_lsi_quantitative_audit_coherence_of_quantitative_frontier d N_c
        ((balaban_rg_uniform_lsi_quantitative_frontier_iff_pair d N_c).2 h)

/-- Coherence: the audit packet field agrees canonically with the one reconstructed
from the quantitative frontier. -/
theorem balaban_rg_uniform_lsi_quantitative_audit_packet_eq_canonical_of_quantitative_audit_coherence
    {d N_c : ℕ} [NeZero N_c]
    (coh : BalabanRGUniformLSIQuantitativeAuditCoherence d N_c) :
    coh.auditPacket =
      balaban_rg_uniform_lsi_quantitative_audit_packet_of_quantitative_frontier d N_c
        coh.quantitativeFrontier := by
  apply Subsingleton.elim

/-- Coherence: the quantitative frontier field agrees canonically with the one reconstructed
from the audit packet. -/
theorem balaban_rg_uniform_lsi_quantitative_frontier_eq_canonical_of_quantitative_audit_coherence
    {d N_c : ℕ} [NeZero N_c]
    (coh : BalabanRGUniformLSIQuantitativeAuditCoherence d N_c) :
    coh.quantitativeFrontier =
      quantitative_frontier_of_balaban_rg_uniform_lsi_quantitative_audit_packet
        coh.auditPacket := by
  apply Subsingleton.elim

/-- Coherence: the rates frontier field agrees canonically with the one reconstructed
from the quantitative frontier. -/
theorem physical_rg_rates_frontier_eq_canonical_of_quantitative_audit_coherence
    {d N_c : ℕ} [NeZero N_c]
    (coh : BalabanRGUniformLSIQuantitativeAuditCoherence d N_c) :
    coh.ratesFrontier =
      physical_rg_rates_frontier_of_balaban_rg_uniform_lsi_quantitative_frontier
        coh.quantitativeFrontier := by
  apply Subsingleton.elim

/-- Coherence: the public frontier field agrees canonically with the one reconstructed
from the quantitative frontier. -/
theorem balaban_rg_uniform_lsi_public_frontier_eq_canonical_of_quantitative_audit_coherence
    {d N_c : ℕ} [NeZero N_c]
    (coh : BalabanRGUniformLSIQuantitativeAuditCoherence d N_c) :
    coh.publicFrontier =
      balaban_rg_uniform_lsi_frontier_of_quantitative_frontier d N_c
        coh.quantitativeFrontier := by
  apply Subsingleton.elim

/-- Coherence: the public facade field agrees canonically with the one reconstructed
from the quantitative frontier. -/
theorem balaban_rg_uniform_lsi_public_facade_eq_canonical_of_quantitative_audit_coherence
    {d N_c : ℕ} [NeZero N_c]
    (coh : BalabanRGUniformLSIQuantitativeAuditCoherence d N_c) :
    coh.publicFacade =
      balaban_rg_uniform_lsi_public_facade_of_quantitative_frontier d N_c
        coh.quantitativeFrontier := by
  apply Subsingleton.elim

/-- Coherence: the quantitative audit coherence hub is propositionally equal to the canonical one
reconstructed from its quantitative frontier. -/
theorem balaban_rg_uniform_lsi_quantitative_audit_coherence_eq_canonical_of_quantitative_frontier
    {d N_c : ℕ} [NeZero N_c]
    (coh : BalabanRGUniformLSIQuantitativeAuditCoherence d N_c) :
    coh =
      balaban_rg_uniform_lsi_quantitative_audit_coherence_of_quantitative_frontier d N_c
        coh.quantitativeFrontier := by
  apply Subsingleton.elim

end YangMills.ClayCore
