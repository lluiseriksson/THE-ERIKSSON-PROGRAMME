import Mathlib
import YangMills.ClayCore.BalabanRG.RGCauchyP81CoherencePacket

namespace YangMills.ClayCore

open scoped BigOperators
open Classical

noncomputable section

/-- Actual theorem-side live target for the RG–Cauchy P81 bottleneck:
there is a weak-coupling threshold above which the single-scale increment
decay bound holds uniformly in β. -/
def RGCauchyP81LiveTarget
    (d N_c : ℕ) [NeZero N_c] [∀ k, ActivityNorm d k] : Prop :=
  ∃ beta0 : ℝ, 0 < beta0 ∧ ∀ β : ℝ, beta0 ≤ β → RGIncrementDecayBound d N_c β

/-- The current interface theorem directly yields the theorem-side live target.
This remains theorem-shaped because `rg_increment_decay_P81` is still the live gap. -/
theorem rg_cauchy_p81_live_target_of_interface
    (d N_c : ℕ) [NeZero N_c] [∀ k, ActivityNorm d k] :
    RGCauchyP81LiveTarget d N_c := by
  refine ⟨1, one_pos, ?_⟩
  intro β hβ
  exact rg_increment_decay_P81 d N_c β hβ

/-- From the theorem-side live target, recover a canonical kernel output packet
by choosing `max beta0 1`. -/
theorem rg_cauchy_p81_kernel_output_of_live_target
    (d N_c : ℕ) [NeZero N_c] [∀ k, ActivityNorm d k]
    (live : RGCauchyP81LiveTarget d N_c) :
    RGCauchyP81KernelOutput d N_c := by
  rcases live with ⟨beta0, hbeta0_pos, hlive⟩
  let β : ℝ := max beta0 1
  have hbeta0_le : beta0 ≤ β := le_max_left _ _
  have h1_le : 1 ≤ β := le_max_right _ _
  have hinc : RGIncrementDecayBound d N_c β := hlive β hbeta0_le
  exact
    ⟨⟨β, h1_le, hinc, increment_decay_implies_cauchy_summability d N_c β hinc⟩⟩

/-- From the theorem-side live target, recover the kernel input packet. -/
theorem rg_cauchy_p81_kernel_input_of_live_target
    (d N_c : ℕ) [NeZero N_c] [∀ k, ActivityNorm d k]
    (live : RGCauchyP81LiveTarget d N_c) :
    RGCauchyP81KernelInput d N_c := by
  exact
    rg_cauchy_p81_kernel_input_of_output d N_c
      (rg_cauchy_p81_kernel_output_of_live_target d N_c live)

/-- From the theorem-side live target, recover the obligation surface. -/
theorem rg_cauchy_p81_obligation_of_live_target
    (d N_c : ℕ) [NeZero N_c] [∀ k, ActivityNorm d k]
    (live : RGCauchyP81LiveTarget d N_c) :
    RGCauchyP81Obligation d N_c := by
  exact
    rg_cauchy_p81_obligation_of_output d N_c
      (rg_cauchy_p81_kernel_output_of_live_target d N_c live)

/-- From an audit packet together with the theorem-side live target, recover the
short public P81 frontier. -/
theorem rg_cauchy_p81_frontier_of_audit_packet_and_live_target
    (d N_c : ℕ) [NeZero N_c] [∀ k, ActivityNorm d k]
    (audit : BalabanRGUniformLSIAuditPacket d N_c)
    (live : RGCauchyP81LiveTarget d N_c) :
    RGCauchyP81Frontier d N_c := by
  exact
    rg_cauchy_p81_frontier_of_audit_packet_and_obligation d N_c audit
      (rg_cauchy_p81_obligation_of_live_target d N_c live)

/-- From an audit packet together with the theorem-side live target, recover the
explicit audit link surface. -/
theorem balaban_rg_uniform_lsi_rg_cauchy_audit_link_of_audit_packet_and_live_target
    (d N_c : ℕ) [NeZero N_c] [∀ k, ActivityNorm d k]
    (audit : BalabanRGUniformLSIAuditPacket d N_c)
    (live : RGCauchyP81LiveTarget d N_c) :
    BalabanRGUniformLSIRGCauchyAuditLink d N_c := by
  exact
    balaban_rg_uniform_lsi_rg_cauchy_audit_link_of_audit_packet_and_obligation d N_c
      audit (rg_cauchy_p81_obligation_of_live_target d N_c live)

/-- From an audit packet together with the theorem-side live target, recover the
coherence packet. -/
theorem rg_cauchy_p81_coherence_packet_of_audit_packet_and_live_target
    (d N_c : ℕ) [NeZero N_c] [∀ k, ActivityNorm d k]
    (audit : BalabanRGUniformLSIAuditPacket d N_c)
    (live : RGCauchyP81LiveTarget d N_c) :
    RGCauchyP81CoherencePacket d N_c := by
  exact
    rg_cauchy_p81_coherence_packet_of_frontier d N_c
      (rg_cauchy_p81_frontier_of_audit_packet_and_live_target d N_c audit live)

/-- The theorem-side live target yields the existential increment-decay surface. -/
theorem rg_increment_decay_bound_of_rg_cauchy_p81_live_target
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (live : RGCauchyP81LiveTarget d N_c) :
    ∃ β : ℝ, 1 ≤ β ∧ RGIncrementDecayBound d N_c β := by
  exact
    rg_increment_decay_bound_of_rg_cauchy_p81_kernel_output
      (rg_cauchy_p81_kernel_output_of_live_target d N_c live)

/-- The theorem-side live target yields the existential RG-Cauchy summability surface. -/
theorem rg_cauchy_summability_bound_of_rg_cauchy_p81_live_target
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (live : RGCauchyP81LiveTarget d N_c) :
    ∃ β : ℝ, 1 ≤ β ∧ RGCauchySummabilityBound d N_c β := by
  exact
    rg_cauchy_summability_bound_of_rg_cauchy_p81_kernel_output
      (rg_cauchy_p81_kernel_output_of_live_target d N_c live)

/-- Coherence: reconstructing the kernel output from the theorem-side live target is
propositionally canonical. -/
theorem rg_cauchy_p81_kernel_output_eq_canonical_of_live_target
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (live : RGCauchyP81LiveTarget d N_c) :
    rg_cauchy_p81_kernel_output_of_live_target d N_c live =
      rg_cauchy_p81_kernel_output_of_obligation d N_c
        (rg_cauchy_p81_obligation_of_live_target d N_c live) := by
  apply Subsingleton.elim

/-- Coherence: reconstructing the kernel input from the theorem-side live target is
propositionally canonical. -/
theorem rg_cauchy_p81_kernel_input_eq_canonical_of_live_target
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (live : RGCauchyP81LiveTarget d N_c) :
    rg_cauchy_p81_kernel_input_of_live_target d N_c live =
      rg_cauchy_p81_kernel_input_of_obligation d N_c
        (rg_cauchy_p81_obligation_of_live_target d N_c live) := by
  apply Subsingleton.elim

end

end YangMills.ClayCore
