import Mathlib
import YangMills.ClayCore.BalabanRG.BalabanRGUniformLSIAuditCoherence
import YangMills.ClayCore.BalabanRG.RGCauchyP81Interface

namespace YangMills.ClayCore

open scoped BigOperators
open Classical

noncomputable section

/-- Explicit kernel input for the first unresolved RG–Cauchy interface theorem:
it packages the existence of a weak-coupling parameter β with the P81 threshold. -/
structure RGCauchyP81KernelInput
    (d N_c : ℕ) [NeZero N_c] [∀ k, ActivityNorm d k] : Prop where
  exists_beta : ∃ β : ℝ, 1 ≤ β

/-- Explicit kernel output for the first unresolved RG–Cauchy interface theorem:
it packages the existence of a β carrying both the single-scale increment decay
and the derived RG-Cauchy summability. -/
structure RGCauchyP81KernelOutput
    (d N_c : ℕ) [NeZero N_c] [∀ k, ActivityNorm d k] : Prop where
  exists_beta :
    ∃ β : ℝ, 1 ≤ β ∧ RGIncrementDecayBound d N_c β ∧ RGCauchySummabilityBound d N_c β

/-- Canonical kernel input from a bare β together with the weak-coupling threshold. -/
theorem rg_cauchy_p81_kernel_input_of_beta
    (d N_c : ℕ) [NeZero N_c] [∀ k, ActivityNorm d k]
    (β : ℝ) (hβ : 1 ≤ β) :
    RGCauchyP81KernelInput d N_c := by
  exact ⟨⟨β, hβ⟩⟩

/-- Canonical kernel output from a bare β together with the weak-coupling threshold. -/
theorem rg_cauchy_p81_kernel_output_of_beta
    (d N_c : ℕ) [NeZero N_c] [∀ k, ActivityNorm d k]
    (β : ℝ) (hβ : 1 ≤ β) :
    RGCauchyP81KernelOutput d N_c := by
  exact
    ⟨⟨β, hβ, rg_increment_decay_P81 d N_c β hβ, rg_cauchy_from_increment_decay d N_c β hβ⟩⟩

/-- Canonical kernel output from the explicit kernel input packet. -/
theorem rg_cauchy_p81_kernel_output_of_input
    (d N_c : ℕ) [NeZero N_c] [∀ k, ActivityNorm d k]
    (input : RGCauchyP81KernelInput d N_c) :
    RGCauchyP81KernelOutput d N_c := by
  rcases input.exists_beta with ⟨β, hβ⟩
  exact rg_cauchy_p81_kernel_output_of_beta d N_c β hβ

/-- Recover the explicit kernel input from the kernel output packet. -/
theorem rg_cauchy_p81_kernel_input_of_output
    (d N_c : ℕ) [NeZero N_c] [∀ k, ActivityNorm d k]
    (output : RGCauchyP81KernelOutput d N_c) :
    RGCauchyP81KernelInput d N_c := by
  rcases output.exists_beta with ⟨β, hβ, _, _⟩
  exact ⟨⟨β, hβ⟩⟩

/-- Projection to the single-scale increment decay bound. -/
theorem rg_increment_decay_bound_of_rg_cauchy_p81_kernel_output
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (output : RGCauchyP81KernelOutput d N_c) :
    ∃ β : ℝ, 1 ≤ β ∧ RGIncrementDecayBound d N_c β := by
  rcases output.exists_beta with ⟨β, hβ, hinc, _⟩
  exact ⟨β, hβ, hinc⟩

/-- Projection to the RG-Cauchy summability bound. -/
theorem rg_cauchy_summability_bound_of_rg_cauchy_p81_kernel_output
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (output : RGCauchyP81KernelOutput d N_c) :
    ∃ β : ℝ, 1 ≤ β ∧ RGCauchySummabilityBound d N_c β := by
  rcases output.exists_beta with ⟨β, hβ, _, hsum⟩
  exact ⟨β, hβ, hsum⟩

/-- Logical normal form: the explicit kernel output is equivalent to the explicit kernel input. -/
theorem rg_cauchy_p81_kernel_output_iff_input
    (d N_c : ℕ) [NeZero N_c] [∀ k, ActivityNorm d k] :
    RGCauchyP81KernelOutput d N_c ↔
      RGCauchyP81KernelInput d N_c := by
  constructor
  · intro output
    exact rg_cauchy_p81_kernel_input_of_output d N_c output
  · intro input
    exact rg_cauchy_p81_kernel_output_of_input d N_c input

/-- Canonical round-trip: input → output → input is propositionally the identity. -/
theorem rg_cauchy_p81_kernel_input_of_output_of_input_eq_canonical
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (input : RGCauchyP81KernelInput d N_c) :
    rg_cauchy_p81_kernel_input_of_output d N_c
      (rg_cauchy_p81_kernel_output_of_input d N_c input) = input := by
  apply Subsingleton.elim

/-- Canonical round-trip: output → input → output is propositionally the identity. -/
theorem rg_cauchy_p81_kernel_output_of_input_of_output_eq_canonical
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (output : RGCauchyP81KernelOutput d N_c) :
    rg_cauchy_p81_kernel_output_of_input d N_c
      (rg_cauchy_p81_kernel_input_of_output d N_c output) = output := by
  apply Subsingleton.elim

/-- Bridge surface linking the current audit-facing lane to the first explicit unresolved
RG–Cauchy kernel. -/
structure BalabanRGUniformLSIRGCauchyAuditLink
    (d N_c : ℕ) [NeZero N_c] [∀ k, ActivityNorm d k] : Prop where
  audit : BalabanRGUniformLSIAuditPacket d N_c
  kernel : RGCauchyP81KernelOutput d N_c

/-- Canonical RG–Cauchy audit link from an audit packet and the explicit kernel input. -/
theorem balaban_rg_uniform_lsi_rg_cauchy_audit_link_of_audit_packet_and_input
    (d N_c : ℕ) [NeZero N_c] [∀ k, ActivityNorm d k]
    (audit : BalabanRGUniformLSIAuditPacket d N_c)
    (input : RGCauchyP81KernelInput d N_c) :
    BalabanRGUniformLSIRGCauchyAuditLink d N_c := by
  exact ⟨audit, rg_cauchy_p81_kernel_output_of_input d N_c input⟩

/-- Canonical RG–Cauchy audit link from the short public frontier and the explicit kernel input. -/
theorem balaban_rg_uniform_lsi_rg_cauchy_audit_link_of_frontier_and_input
    (d N_c : ℕ) [NeZero N_c] [∀ k, ActivityNorm d k]
    (frontier : BalabanRGUniformLSIFrontier d N_c)
    (input : RGCauchyP81KernelInput d N_c) :
    BalabanRGUniformLSIRGCauchyAuditLink d N_c := by
  exact
    balaban_rg_uniform_lsi_rg_cauchy_audit_link_of_audit_packet_and_input d N_c
      (balaban_rg_uniform_lsi_audit_packet_of_frontier frontier) input

/-- Projection to the audit packet. -/
theorem audit_packet_of_balaban_rg_uniform_lsi_rg_cauchy_audit_link
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (link : BalabanRGUniformLSIRGCauchyAuditLink d N_c) :
    BalabanRGUniformLSIAuditPacket d N_c := by
  exact link.audit

/-- Projection to the explicit kernel output packet. -/
theorem rg_cauchy_p81_kernel_output_of_balaban_rg_uniform_lsi_rg_cauchy_audit_link
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (link : BalabanRGUniformLSIRGCauchyAuditLink d N_c) :
    RGCauchyP81KernelOutput d N_c := by
  exact link.kernel

/-- Projection to the explicit kernel input packet. -/
theorem rg_cauchy_p81_kernel_input_of_balaban_rg_uniform_lsi_rg_cauchy_audit_link
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (link : BalabanRGUniformLSIRGCauchyAuditLink d N_c) :
    RGCauchyP81KernelInput d N_c := by
  exact rg_cauchy_p81_kernel_input_of_output d N_c link.kernel

/-- Projection to the single-scale increment decay bound. -/
theorem rg_increment_decay_bound_of_balaban_rg_uniform_lsi_rg_cauchy_audit_link
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (link : BalabanRGUniformLSIRGCauchyAuditLink d N_c) :
    ∃ β : ℝ, 1 ≤ β ∧ RGIncrementDecayBound d N_c β := by
  exact rg_increment_decay_bound_of_rg_cauchy_p81_kernel_output link.kernel

/-- Projection to the RG-Cauchy summability bound. -/
theorem rg_cauchy_summability_bound_of_balaban_rg_uniform_lsi_rg_cauchy_audit_link
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (link : BalabanRGUniformLSIRGCauchyAuditLink d N_c) :
    ∃ β : ℝ, 1 ≤ β ∧ RGCauchySummabilityBound d N_c β := by
  exact rg_cauchy_summability_bound_of_rg_cauchy_p81_kernel_output link.kernel

/-- Logical normal form: the RG–Cauchy audit link is equivalent to an audit packet together
with the explicit kernel input. -/
theorem balaban_rg_uniform_lsi_rg_cauchy_audit_link_iff_audit_packet_and_input
    (d N_c : ℕ) [NeZero N_c] [∀ k, ActivityNorm d k] :
    BalabanRGUniformLSIRGCauchyAuditLink d N_c ↔
      (BalabanRGUniformLSIAuditPacket d N_c ∧ RGCauchyP81KernelInput d N_c) := by
  constructor
  · intro link
    exact
      ⟨audit_packet_of_balaban_rg_uniform_lsi_rg_cauchy_audit_link link,
        rg_cauchy_p81_kernel_input_of_balaban_rg_uniform_lsi_rg_cauchy_audit_link link⟩
  · intro h
    exact
      balaban_rg_uniform_lsi_rg_cauchy_audit_link_of_audit_packet_and_input d N_c
        h.1 h.2

/-- Canonical round-trip: (audit,input) → link → (audit,input) is propositionally the identity. -/
theorem balaban_rg_uniform_lsi_rg_cauchy_audit_link_and_roundtrip_eq_canonical
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (audit : BalabanRGUniformLSIAuditPacket d N_c)
    (input : RGCauchyP81KernelInput d N_c) :
    (show BalabanRGUniformLSIAuditPacket d N_c ∧ RGCauchyP81KernelInput d N_c from
      ⟨ audit_packet_of_balaban_rg_uniform_lsi_rg_cauchy_audit_link
          (balaban_rg_uniform_lsi_rg_cauchy_audit_link_of_audit_packet_and_input d N_c audit input),
        rg_cauchy_p81_kernel_input_of_balaban_rg_uniform_lsi_rg_cauchy_audit_link
          (balaban_rg_uniform_lsi_rg_cauchy_audit_link_of_audit_packet_and_input d N_c audit input) ⟩)
    =
    (show BalabanRGUniformLSIAuditPacket d N_c ∧ RGCauchyP81KernelInput d N_c from
      ⟨audit, input⟩) := by
  apply Subsingleton.elim

/-- Canonical round-trip: link → (audit,input) → link is propositionally the identity. -/
theorem balaban_rg_uniform_lsi_rg_cauchy_audit_link_of_pair_of_link_eq_canonical
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (link : BalabanRGUniformLSIRGCauchyAuditLink d N_c) :
    balaban_rg_uniform_lsi_rg_cauchy_audit_link_of_audit_packet_and_input d N_c
      (audit_packet_of_balaban_rg_uniform_lsi_rg_cauchy_audit_link link)
      (rg_cauchy_p81_kernel_input_of_balaban_rg_uniform_lsi_rg_cauchy_audit_link link)
      = link := by
  apply Subsingleton.elim

end

end YangMills.ClayCore
