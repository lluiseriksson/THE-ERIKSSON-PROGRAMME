import Mathlib
import YangMills.ClayCore.BalabanRG.RGCauchyP81Obligation

namespace YangMills.ClayCore

open scoped BigOperators
open Classical

noncomputable section

/-- Single public frontier for the current explicit RG–Cauchy P81 bottleneck:
it packages exactly the current live pair, namely an audit packet together
with the P81 obligation surface. -/
structure RGCauchyP81Frontier
    (d N_c : ℕ) [NeZero N_c] [∀ k, ActivityNorm d k] : Prop where
  audit : BalabanRGUniformLSIAuditPacket d N_c
  obligation : RGCauchyP81Obligation d N_c

/-- Canonical frontier from an audit packet and the P81 obligation surface. -/
theorem rg_cauchy_p81_frontier_of_audit_packet_and_obligation
    (d N_c : ℕ) [NeZero N_c] [∀ k, ActivityNorm d k]
    (audit : BalabanRGUniformLSIAuditPacket d N_c)
    (ob : RGCauchyP81Obligation d N_c) :
    RGCauchyP81Frontier d N_c := by
  exact ⟨audit, ob⟩

/-- Canonical frontier from the audit link to the P81 kernel. -/
theorem rg_cauchy_p81_frontier_of_audit_link
    (d N_c : ℕ) [NeZero N_c] [∀ k, ActivityNorm d k]
    (link : BalabanRGUniformLSIRGCauchyAuditLink d N_c) :
    RGCauchyP81Frontier d N_c := by
  exact ⟨link.audit, rg_cauchy_p81_obligation_of_audit_link d N_c link⟩

/-- Projection to the audit packet. -/
theorem audit_packet_of_rg_cauchy_p81_frontier
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (frontier : RGCauchyP81Frontier d N_c) :
    BalabanRGUniformLSIAuditPacket d N_c := by
  exact frontier.audit

/-- Projection to the P81 obligation surface. -/
theorem obligation_of_rg_cauchy_p81_frontier
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (frontier : RGCauchyP81Frontier d N_c) :
    RGCauchyP81Obligation d N_c := by
  exact frontier.obligation

/-- Projection to the explicit kernel output packet. -/
theorem rg_cauchy_p81_kernel_output_of_frontier
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (frontier : RGCauchyP81Frontier d N_c) :
    RGCauchyP81KernelOutput d N_c := by
  exact rg_cauchy_p81_kernel_output_of_obligation d N_c frontier.obligation

/-- Projection to the explicit kernel input packet. -/
theorem rg_cauchy_p81_kernel_input_of_frontier
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (frontier : RGCauchyP81Frontier d N_c) :
    RGCauchyP81KernelInput d N_c := by
  exact rg_cauchy_p81_kernel_input_of_obligation d N_c frontier.obligation

/-- Projection to the P81 increment decay side. -/
theorem rg_increment_decay_bound_of_rg_cauchy_p81_frontier
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (frontier : RGCauchyP81Frontier d N_c) :
    ∃ β : ℝ, 1 ≤ β ∧ RGIncrementDecayBound d N_c β := by
  exact rg_increment_decay_bound_of_rg_cauchy_p81_obligation frontier.obligation

/-- Projection to the RG-Cauchy summability side. -/
theorem rg_cauchy_summability_bound_of_rg_cauchy_p81_frontier
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (frontier : RGCauchyP81Frontier d N_c) :
    ∃ β : ℝ, 1 ≤ β ∧ RGCauchySummabilityBound d N_c β := by
  exact rg_cauchy_summability_bound_of_rg_cauchy_p81_obligation frontier.obligation

/-- Logical normal form: the P81 frontier is equivalent to an audit packet together
with the P81 obligation surface. -/
theorem rg_cauchy_p81_frontier_iff_audit_packet_and_obligation
    (d N_c : ℕ) [NeZero N_c] [∀ k, ActivityNorm d k] :
    RGCauchyP81Frontier d N_c ↔
      (BalabanRGUniformLSIAuditPacket d N_c ∧ RGCauchyP81Obligation d N_c) := by
  constructor
  · intro frontier
    exact ⟨frontier.audit, frontier.obligation⟩
  · intro h
    exact rg_cauchy_p81_frontier_of_audit_packet_and_obligation d N_c h.1 h.2

/-- Logical normal form: the P81 frontier is equivalent to the audit link surface. -/
theorem rg_cauchy_p81_frontier_iff_audit_link
    (d N_c : ℕ) [NeZero N_c] [∀ k, ActivityNorm d k] :
    RGCauchyP81Frontier d N_c ↔ BalabanRGUniformLSIRGCauchyAuditLink d N_c := by
  constructor
  · intro frontier
    exact
      balaban_rg_uniform_lsi_rg_cauchy_audit_link_of_audit_packet_and_obligation d N_c
        frontier.audit frontier.obligation
  · intro link
    exact rg_cauchy_p81_frontier_of_audit_link d N_c link

/-- Canonical round-trip: (audit, obligation) → frontier → (audit, obligation)
is propositionally the identity. -/
theorem rg_cauchy_p81_frontier_and_roundtrip_eq_canonical
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (audit : BalabanRGUniformLSIAuditPacket d N_c)
    (ob : RGCauchyP81Obligation d N_c) :
    (show BalabanRGUniformLSIAuditPacket d N_c ∧ RGCauchyP81Obligation d N_c from
      ⟨ audit_packet_of_rg_cauchy_p81_frontier
          (rg_cauchy_p81_frontier_of_audit_packet_and_obligation d N_c audit ob),
        obligation_of_rg_cauchy_p81_frontier
          (rg_cauchy_p81_frontier_of_audit_packet_and_obligation d N_c audit ob) ⟩)
    =
    (show BalabanRGUniformLSIAuditPacket d N_c ∧ RGCauchyP81Obligation d N_c from
      ⟨audit, ob⟩) := by
  apply Subsingleton.elim

/-- Canonical round-trip: frontier → audit-link → frontier
is propositionally the identity. -/
theorem rg_cauchy_p81_frontier_of_audit_link_of_frontier_eq_canonical
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (frontier : RGCauchyP81Frontier d N_c) :
    rg_cauchy_p81_frontier_of_audit_link d N_c
      (balaban_rg_uniform_lsi_rg_cauchy_audit_link_of_audit_packet_and_obligation d N_c
        frontier.audit frontier.obligation)
      = frontier := by
  apply Subsingleton.elim

/-- Canonical round-trip: audit-link → frontier → audit-link
is propositionally the identity. -/
theorem balaban_rg_uniform_lsi_rg_cauchy_audit_link_of_frontier_of_audit_link_eq_canonical
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (link : BalabanRGUniformLSIRGCauchyAuditLink d N_c) :
    balaban_rg_uniform_lsi_rg_cauchy_audit_link_of_audit_packet_and_obligation d N_c
      (audit_packet_of_rg_cauchy_p81_frontier
        (rg_cauchy_p81_frontier_of_audit_link d N_c link))
      (obligation_of_rg_cauchy_p81_frontier
        (rg_cauchy_p81_frontier_of_audit_link d N_c link))
      = link := by
  apply Subsingleton.elim

end

end YangMills.ClayCore
