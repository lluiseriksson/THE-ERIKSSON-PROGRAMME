import Mathlib
import YangMills.ClayCore.BalabanRG.RGCauchyP81Kernel

namespace YangMills.ClayCore

open scoped BigOperators
open Classical

noncomputable section

/-- Single explicit live obligation surface for the first unresolved RG–Cauchy theorem:
it packages the existence of a β carrying both the P81 single-scale increment decay
bound and the derived RG-Cauchy summability consequence. -/
structure RGCauchyP81Obligation
    (d N_c : ℕ) [NeZero N_c] [∀ k, ActivityNorm d k] : Prop where
  exists_beta :
    ∃ β : ℝ, 1 ≤ β ∧ RGIncrementDecayBound d N_c β ∧ RGCauchySummabilityBound d N_c β

/-- Canonical obligation from a bare β together with the weak-coupling threshold. -/
theorem rg_cauchy_p81_obligation_of_beta
    (d N_c : ℕ) [NeZero N_c] [∀ k, ActivityNorm d k]
    (β : ℝ) (hβ : 1 ≤ β) :
    RGCauchyP81Obligation d N_c := by
  exact
    ⟨⟨β, hβ, rg_increment_decay_P81 d N_c β hβ, rg_cauchy_from_increment_decay d N_c β hβ⟩⟩

/-- Canonical obligation from the explicit kernel input packet. -/
theorem rg_cauchy_p81_obligation_of_input
    (d N_c : ℕ) [NeZero N_c] [∀ k, ActivityNorm d k]
    (input : RGCauchyP81KernelInput d N_c) :
    RGCauchyP81Obligation d N_c := by
  rcases input.exists_beta with ⟨β, hβ⟩
  exact rg_cauchy_p81_obligation_of_beta d N_c β hβ

/-- Canonical obligation from the explicit kernel output packet. -/
theorem rg_cauchy_p81_obligation_of_output
    (d N_c : ℕ) [NeZero N_c] [∀ k, ActivityNorm d k]
    (output : RGCauchyP81KernelOutput d N_c) :
    RGCauchyP81Obligation d N_c := by
  exact ⟨output.exists_beta⟩

/-- Canonical obligation from the audit link to the P81 kernel. -/
theorem rg_cauchy_p81_obligation_of_audit_link
    (d N_c : ℕ) [NeZero N_c] [∀ k, ActivityNorm d k]
    (link : BalabanRGUniformLSIRGCauchyAuditLink d N_c) :
    RGCauchyP81Obligation d N_c := by
  exact rg_cauchy_p81_obligation_of_output d N_c link.kernel

/-- Recover the explicit kernel output packet from the obligation surface. -/
theorem rg_cauchy_p81_kernel_output_of_obligation
    (d N_c : ℕ) [NeZero N_c] [∀ k, ActivityNorm d k]
    (ob : RGCauchyP81Obligation d N_c) :
    RGCauchyP81KernelOutput d N_c := by
  exact ⟨ob.exists_beta⟩

/-- Recover the explicit kernel input packet from the obligation surface. -/
theorem rg_cauchy_p81_kernel_input_of_obligation
    (d N_c : ℕ) [NeZero N_c] [∀ k, ActivityNorm d k]
    (ob : RGCauchyP81Obligation d N_c) :
    RGCauchyP81KernelInput d N_c := by
  rcases ob.exists_beta with ⟨β, hβ, _, _⟩
  exact ⟨⟨β, hβ⟩⟩

/-- Projection to the P81 increment decay side of the obligation. -/
theorem rg_increment_decay_bound_of_rg_cauchy_p81_obligation
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (ob : RGCauchyP81Obligation d N_c) :
    ∃ β : ℝ, 1 ≤ β ∧ RGIncrementDecayBound d N_c β := by
  rcases ob.exists_beta with ⟨β, hβ, hinc, _⟩
  exact ⟨β, hβ, hinc⟩

/-- Projection to the RG-Cauchy summability side of the obligation. -/
theorem rg_cauchy_summability_bound_of_rg_cauchy_p81_obligation
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (ob : RGCauchyP81Obligation d N_c) :
    ∃ β : ℝ, 1 ≤ β ∧ RGCauchySummabilityBound d N_c β := by
  rcases ob.exists_beta with ⟨β, hβ, _, hsum⟩
  exact ⟨β, hβ, hsum⟩

/-- Logical normal form: the obligation surface is equivalent to the kernel input. -/
theorem rg_cauchy_p81_obligation_iff_input
    (d N_c : ℕ) [NeZero N_c] [∀ k, ActivityNorm d k] :
    RGCauchyP81Obligation d N_c ↔ RGCauchyP81KernelInput d N_c := by
  constructor
  · intro ob
    exact rg_cauchy_p81_kernel_input_of_obligation d N_c ob
  · intro input
    exact rg_cauchy_p81_obligation_of_input d N_c input

/-- Logical normal form: the obligation surface is equivalent to the kernel output. -/
theorem rg_cauchy_p81_obligation_iff_output
    (d N_c : ℕ) [NeZero N_c] [∀ k, ActivityNorm d k] :
    RGCauchyP81Obligation d N_c ↔ RGCauchyP81KernelOutput d N_c := by
  constructor
  · intro ob
    exact rg_cauchy_p81_kernel_output_of_obligation d N_c ob
  · intro output
    exact rg_cauchy_p81_obligation_of_output d N_c output

/-- Canonical bridge from an audit packet plus the obligation surface to the RG–Cauchy audit link. -/
theorem balaban_rg_uniform_lsi_rg_cauchy_audit_link_of_audit_packet_and_obligation
    (d N_c : ℕ) [NeZero N_c] [∀ k, ActivityNorm d k]
    (audit : BalabanRGUniformLSIAuditPacket d N_c)
    (ob : RGCauchyP81Obligation d N_c) :
    BalabanRGUniformLSIRGCauchyAuditLink d N_c := by
  exact ⟨audit, rg_cauchy_p81_kernel_output_of_obligation d N_c ob⟩

/-- Logical normal form: the RG–Cauchy audit link is equivalent to an audit packet together
with the explicit obligation surface. -/
theorem balaban_rg_uniform_lsi_rg_cauchy_audit_link_iff_audit_packet_and_obligation
    (d N_c : ℕ) [NeZero N_c] [∀ k, ActivityNorm d k] :
    BalabanRGUniformLSIRGCauchyAuditLink d N_c ↔
      (BalabanRGUniformLSIAuditPacket d N_c ∧ RGCauchyP81Obligation d N_c) := by
  constructor
  · intro link
    exact ⟨link.audit, rg_cauchy_p81_obligation_of_audit_link d N_c link⟩
  · intro h
    exact
      balaban_rg_uniform_lsi_rg_cauchy_audit_link_of_audit_packet_and_obligation d N_c
        h.1 h.2

/-- Canonical round-trip: obligation → output → obligation is propositionally the identity. -/
theorem rg_cauchy_p81_obligation_of_output_of_obligation_eq_canonical
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (ob : RGCauchyP81Obligation d N_c) :
    rg_cauchy_p81_obligation_of_output d N_c
      (rg_cauchy_p81_kernel_output_of_obligation d N_c ob) = ob := by
  apply Subsingleton.elim

/-- Canonical round-trip: output → obligation → output is propositionally the identity. -/
theorem rg_cauchy_p81_kernel_output_of_obligation_of_output_eq_canonical
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (output : RGCauchyP81KernelOutput d N_c) :
    rg_cauchy_p81_kernel_output_of_obligation d N_c
      (rg_cauchy_p81_obligation_of_output d N_c output) = output := by
  apply Subsingleton.elim

/-- Canonical round-trip: (audit, obligation) → link → (audit, obligation) is propositionally the identity. -/
theorem balaban_rg_uniform_lsi_rg_cauchy_audit_link_and_obligation_roundtrip_eq_canonical
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (audit : BalabanRGUniformLSIAuditPacket d N_c)
    (ob : RGCauchyP81Obligation d N_c) :
    (show BalabanRGUniformLSIAuditPacket d N_c ∧ RGCauchyP81Obligation d N_c from
      ⟨ audit_packet_of_balaban_rg_uniform_lsi_rg_cauchy_audit_link
          (balaban_rg_uniform_lsi_rg_cauchy_audit_link_of_audit_packet_and_obligation d N_c audit ob),
        rg_cauchy_p81_obligation_of_audit_link d N_c
          (balaban_rg_uniform_lsi_rg_cauchy_audit_link_of_audit_packet_and_obligation d N_c audit ob) ⟩)
    =
    (show BalabanRGUniformLSIAuditPacket d N_c ∧ RGCauchyP81Obligation d N_c from
      ⟨audit, ob⟩) := by
  apply Subsingleton.elim

/-- Canonical round-trip: link → (audit, obligation) → link is propositionally the identity. -/
theorem balaban_rg_uniform_lsi_rg_cauchy_audit_link_of_audit_and_obligation_of_link_eq_canonical
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (link : BalabanRGUniformLSIRGCauchyAuditLink d N_c) :
    balaban_rg_uniform_lsi_rg_cauchy_audit_link_of_audit_packet_and_obligation d N_c
      (audit_packet_of_balaban_rg_uniform_lsi_rg_cauchy_audit_link link)
      (rg_cauchy_p81_obligation_of_audit_link d N_c link)
      = link := by
  apply Subsingleton.elim

end

end YangMills.ClayCore
