import Mathlib
import YangMills.ClayCore.BalabanRG.BalabanRGUniformLSIQuantitativeP81LiveTargetBridge

namespace YangMills.ClayCore

open scoped BigOperators
open Classical
noncomputable section

/-- Bridge from the quantitative theorem-side P81 kernel packet to the exact interface theorem
symbol `rg_increment_decay_P81`. -/
def BalabanRGUniformLSIQuantitativeP81InterfaceBridge
    (d N_c : ℕ) [NeZero N_c] [∀ k, ActivityNorm d k] : Prop :=
  BalabanRGUniformLSIQuantitativeP81KernelPacket d N_c

/-- Canonical interface bridge from the quantitative P81 kernel packet. -/
theorem balaban_rg_uniform_lsi_quantitative_p81_interface_bridge_of_quantitative_p81_kernel_packet
    (d N_c : ℕ) [NeZero N_c] [∀ k, ActivityNorm d k]
    (packet : BalabanRGUniformLSIQuantitativeP81KernelPacket d N_c) :
    BalabanRGUniformLSIQuantitativeP81InterfaceBridge d N_c := by
  exact packet

/-- Canonical interface bridge from the direct quantitative frontier together with the theorem-side
live target. -/
theorem balaban_rg_uniform_lsi_quantitative_p81_interface_bridge_of_quantitative_frontier_and_live_target
    (d N_c : ℕ) [NeZero N_c] [∀ k, ActivityNorm d k]
    (frontier : BalabanRGUniformLSIQuantitativeFrontier d N_c)
    (live : RGCauchyP81LiveTarget d N_c) :
    BalabanRGUniformLSIQuantitativeP81InterfaceBridge d N_c := by
  exact
    balaban_rg_uniform_lsi_quantitative_p81_kernel_packet_of_quantitative_frontier_and_live_target
      d N_c frontier live

/-- Canonical interface bridge from the quantitative P81 chosen-beta packet. -/
theorem balaban_rg_uniform_lsi_quantitative_p81_interface_bridge_of_quantitative_p81_chosen_beta_packet
    (d N_c : ℕ) [NeZero N_c] [∀ k, ActivityNorm d k]
    (packet : BalabanRGUniformLSIQuantitativeP81ChosenBetaPacket d N_c) :
    BalabanRGUniformLSIQuantitativeP81InterfaceBridge d N_c := by
  exact
    balaban_rg_uniform_lsi_quantitative_p81_kernel_packet_of_quantitative_p81_chosen_beta_packet
      d N_c packet

/-- Canonical interface bridge from the quantitative P81 witness packet. -/
theorem balaban_rg_uniform_lsi_quantitative_p81_interface_bridge_of_quantitative_p81_witness_packet
    (d N_c : ℕ) [NeZero N_c] [∀ k, ActivityNorm d k]
    (packet : BalabanRGUniformLSIQuantitativeP81WitnessPacket d N_c) :
    BalabanRGUniformLSIQuantitativeP81InterfaceBridge d N_c := by
  exact
    balaban_rg_uniform_lsi_quantitative_p81_kernel_packet_of_quantitative_p81_witness_packet
      d N_c packet

/-- Canonical interface bridge from the quantitative P81 obstruction coherence hub. -/
theorem balaban_rg_uniform_lsi_quantitative_p81_interface_bridge_of_quantitative_p81_obstruction_coherence
    (d N_c : ℕ) [NeZero N_c] [∀ k, ActivityNorm d k]
    (coh : BalabanRGUniformLSIQuantitativeP81ObstructionCoherence d N_c) :
    BalabanRGUniformLSIQuantitativeP81InterfaceBridge d N_c := by
  exact
    balaban_rg_uniform_lsi_quantitative_p81_kernel_packet_of_quantitative_p81_obstruction_coherence
      d N_c coh

/-- Canonical interface bridge from the quantitative P81 obstruction packet. -/
theorem balaban_rg_uniform_lsi_quantitative_p81_interface_bridge_of_quantitative_p81_obstruction_packet
    (d N_c : ℕ) [NeZero N_c] [∀ k, ActivityNorm d k]
    (packet : BalabanRGUniformLSIQuantitativeP81ObstructionPacket d N_c) :
    BalabanRGUniformLSIQuantitativeP81InterfaceBridge d N_c := by
  exact
    balaban_rg_uniform_lsi_quantitative_p81_kernel_packet_of_quantitative_p81_obstruction_packet
      d N_c packet

/-- Canonical interface bridge from the quantitative P81 coherence hub together with the
theorem-side live target. -/
theorem balaban_rg_uniform_lsi_quantitative_p81_interface_bridge_of_quantitative_p81_coherence_and_live_target
    (d N_c : ℕ) [NeZero N_c] [∀ k, ActivityNorm d k]
    (coh : BalabanRGUniformLSIQuantitativeP81Coherence d N_c)
    (live : RGCauchyP81LiveTarget d N_c) :
    BalabanRGUniformLSIQuantitativeP81InterfaceBridge d N_c := by
  exact
    balaban_rg_uniform_lsi_quantitative_p81_kernel_packet_of_quantitative_p81_coherence_and_live_target
      d N_c coh live

/-- Canonical interface bridge from the quantitative P81 packet. -/
theorem balaban_rg_uniform_lsi_quantitative_p81_interface_bridge_of_quantitative_p81_packet
    (d N_c : ℕ) [NeZero N_c] [∀ k, ActivityNorm d k]
    (packet : BalabanRGUniformLSIQuantitativeP81Packet d N_c) :
    BalabanRGUniformLSIQuantitativeP81InterfaceBridge d N_c := by
  exact
    balaban_rg_uniform_lsi_quantitative_p81_kernel_packet_of_quantitative_p81_packet
      d N_c packet

/-- Canonical interface bridge from the quantitative load-bearing coherence hub together with the
theorem-side live target. -/
theorem balaban_rg_uniform_lsi_quantitative_p81_interface_bridge_of_quantitative_load_bearing_coherence_and_live_target
    (d N_c : ℕ) [NeZero N_c] [∀ k, ActivityNorm d k]
    (coh : BalabanRGUniformLSIQuantitativeLoadBearingCoherence d N_c)
    (live : RGCauchyP81LiveTarget d N_c) :
    BalabanRGUniformLSIQuantitativeP81InterfaceBridge d N_c := by
  exact
    balaban_rg_uniform_lsi_quantitative_p81_kernel_packet_of_quantitative_load_bearing_coherence_and_live_target
      d N_c coh live

/-- Canonical interface bridge from the quantitative audit packet together with the theorem-side
live target. -/
theorem balaban_rg_uniform_lsi_quantitative_p81_interface_bridge_of_quantitative_audit_packet_and_live_target
    (d N_c : ℕ) [NeZero N_c] [∀ k, ActivityNorm d k]
    (packet : BalabanRGUniformLSIQuantitativeAuditPacket d N_c)
    (live : RGCauchyP81LiveTarget d N_c) :
    BalabanRGUniformLSIQuantitativeP81InterfaceBridge d N_c := by
  exact
    balaban_rg_uniform_lsi_quantitative_p81_kernel_packet_of_quantitative_audit_packet_and_live_target
      d N_c packet live

/-- Canonical interface bridge from the quantitative audit coherence hub together with the
theorem-side live target. -/
theorem balaban_rg_uniform_lsi_quantitative_p81_interface_bridge_of_quantitative_audit_coherence_and_live_target
    (d N_c : ℕ) [NeZero N_c] [∀ k, ActivityNorm d k]
    (coh : BalabanRGUniformLSIQuantitativeAuditCoherence d N_c)
    (live : RGCauchyP81LiveTarget d N_c) :
    BalabanRGUniformLSIQuantitativeP81InterfaceBridge d N_c := by
  exact
    balaban_rg_uniform_lsi_quantitative_p81_kernel_packet_of_quantitative_audit_coherence_and_live_target
      d N_c coh live

/-- Projection back to the quantitative P81 kernel packet. -/
theorem quantitative_p81_kernel_packet_of_balaban_rg_uniform_lsi_quantitative_p81_interface_bridge
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (bridge : BalabanRGUniformLSIQuantitativeP81InterfaceBridge d N_c) :
    BalabanRGUniformLSIQuantitativeP81KernelPacket d N_c := by
  exact bridge

/-- Canonically chosen β carried by the interface bridge. -/
def chosen_beta_of_balaban_rg_uniform_lsi_quantitative_p81_interface_bridge
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (bridge : BalabanRGUniformLSIQuantitativeP81InterfaceBridge d N_c) : ℝ :=
  chosen_beta_of_balaban_rg_uniform_lsi_quantitative_p81_kernel_packet bridge

/-- The chosen β satisfies `1 ≤ β`. -/
theorem chosen_beta_ge_one_of_balaban_rg_uniform_lsi_quantitative_p81_interface_bridge
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (bridge : BalabanRGUniformLSIQuantitativeP81InterfaceBridge d N_c) :
    1 ≤ chosen_beta_of_balaban_rg_uniform_lsi_quantitative_p81_interface_bridge bridge := by
  simpa [chosen_beta_of_balaban_rg_uniform_lsi_quantitative_p81_interface_bridge] using
    chosen_beta_ge_one_of_balaban_rg_uniform_lsi_quantitative_p81_kernel_packet bridge

/-- Exact interface theorem evaluated at the canonical chosen β carried by the quantitative route. -/
theorem rg_increment_decay_P81_at_chosen_beta_of_balaban_rg_uniform_lsi_quantitative_p81_interface_bridge
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (bridge : BalabanRGUniformLSIQuantitativeP81InterfaceBridge d N_c) :
    RGIncrementDecayBound d N_c
      (chosen_beta_of_balaban_rg_uniform_lsi_quantitative_p81_interface_bridge bridge) := by
  exact
    rg_increment_decay_P81 d N_c
      (chosen_beta_of_balaban_rg_uniform_lsi_quantitative_p81_interface_bridge bridge)
      (chosen_beta_ge_one_of_balaban_rg_uniform_lsi_quantitative_p81_interface_bridge bridge)

/-- Bridge coherence: the exact interface theorem at the canonical chosen β agrees canonically
with the bound already carried by the quantitative kernel packet. -/
theorem rg_increment_decay_P81_at_chosen_beta_eq_canonical_of_balaban_rg_uniform_lsi_quantitative_p81_interface_bridge
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (bridge : BalabanRGUniformLSIQuantitativeP81InterfaceBridge d N_c) :
    rg_increment_decay_P81_at_chosen_beta_of_balaban_rg_uniform_lsi_quantitative_p81_interface_bridge bridge =
      chosen_beta_increment_decay_bound_of_balaban_rg_uniform_lsi_quantitative_p81_kernel_packet
        (quantitative_p81_kernel_packet_of_balaban_rg_uniform_lsi_quantitative_p81_interface_bridge bridge) := by
  apply Subsingleton.elim

/-- Exact derived summability theorem evaluated at the canonical chosen β carried by the
quantitative route. -/
theorem rg_cauchy_from_increment_decay_at_chosen_beta_of_balaban_rg_uniform_lsi_quantitative_p81_interface_bridge
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (bridge : BalabanRGUniformLSIQuantitativeP81InterfaceBridge d N_c) :
    RGCauchySummabilityBound d N_c
      (chosen_beta_of_balaban_rg_uniform_lsi_quantitative_p81_interface_bridge bridge) := by
  exact
    rg_cauchy_from_increment_decay d N_c
      (chosen_beta_of_balaban_rg_uniform_lsi_quantitative_p81_interface_bridge bridge)
      (chosen_beta_ge_one_of_balaban_rg_uniform_lsi_quantitative_p81_interface_bridge bridge)

/-- Bridge coherence: the exact derived summability theorem at the canonical chosen β agrees
canonically with the bound already carried by the quantitative kernel packet. -/
theorem rg_cauchy_from_increment_decay_at_chosen_beta_eq_canonical_of_balaban_rg_uniform_lsi_quantitative_p81_interface_bridge
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (bridge : BalabanRGUniformLSIQuantitativeP81InterfaceBridge d N_c) :
    rg_cauchy_from_increment_decay_at_chosen_beta_of_balaban_rg_uniform_lsi_quantitative_p81_interface_bridge bridge =
      chosen_beta_cauchy_summability_bound_of_balaban_rg_uniform_lsi_quantitative_p81_kernel_packet
        (quantitative_p81_kernel_packet_of_balaban_rg_uniform_lsi_quantitative_p81_interface_bridge bridge) := by
  apply Subsingleton.elim

/-- Logical normal form: the interface bridge is equivalent to the quantitative P81 kernel packet. -/
theorem balaban_rg_uniform_lsi_quantitative_p81_interface_bridge_iff_quantitative_p81_kernel_packet
    (d N_c : ℕ) [NeZero N_c] [∀ k, ActivityNorm d k] :
    BalabanRGUniformLSIQuantitativeP81InterfaceBridge d N_c ↔
      BalabanRGUniformLSIQuantitativeP81KernelPacket d N_c := by
  constructor
  · intro bridge
    exact bridge
  · intro packet
    exact packet

/-- Logical normal form: the interface bridge is equivalent to the pair consisting of the direct
quantitative frontier and the theorem-side live target. -/
theorem balaban_rg_uniform_lsi_quantitative_p81_interface_bridge_iff_quantitative_frontier_and_live_target
    (d N_c : ℕ) [NeZero N_c] [∀ k, ActivityNorm d k] :
    BalabanRGUniformLSIQuantitativeP81InterfaceBridge d N_c ↔
      (BalabanRGUniformLSIQuantitativeFrontier d N_c ∧ RGCauchyP81LiveTarget d N_c) := by
  constructor
  · intro bridge
    exact
      ⟨ quantitative_frontier_of_balaban_rg_uniform_lsi_quantitative_p81_kernel_packet bridge,
        theorem_live_target_of_balaban_rg_uniform_lsi_quantitative_p81_kernel_packet bridge ⟩
  · intro h
    exact
      balaban_rg_uniform_lsi_quantitative_p81_interface_bridge_of_quantitative_frontier_and_live_target
        d N_c h.1 h.2

end

end YangMills.ClayCore
