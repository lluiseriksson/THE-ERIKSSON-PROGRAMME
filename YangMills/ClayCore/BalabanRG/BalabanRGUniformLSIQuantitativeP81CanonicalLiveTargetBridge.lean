import Mathlib
import YangMills.ClayCore.BalabanRG.BalabanRGUniformLSIQuantitativeP81InterfaceBridge

namespace YangMills.ClayCore

open scoped BigOperators
open Classical
noncomputable section

/-- Bridge from the quantitative theorem-side interface route to the canonical standard live
target of threshold `β₀ = 1`. -/
def BalabanRGUniformLSIQuantitativeP81CanonicalLiveTargetBridge
    (d N_c : ℕ) [NeZero N_c] [∀ k, ActivityNorm d k] : Prop :=
  BalabanRGUniformLSIQuantitativeP81InterfaceBridge d N_c

/-- Canonical bridge from the quantitative P81 interface bridge. -/
theorem balaban_rg_uniform_lsi_quantitative_p81_canonical_live_target_bridge_of_quantitative_p81_interface_bridge
    (d N_c : ℕ) [NeZero N_c] [∀ k, ActivityNorm d k]
    (bridge : BalabanRGUniformLSIQuantitativeP81InterfaceBridge d N_c) :
    BalabanRGUniformLSIQuantitativeP81CanonicalLiveTargetBridge d N_c := by
  exact bridge

/-- Canonical bridge from the direct quantitative frontier together with the theorem-side live
target. -/
theorem balaban_rg_uniform_lsi_quantitative_p81_canonical_live_target_bridge_of_quantitative_frontier_and_live_target
    (d N_c : ℕ) [NeZero N_c] [∀ k, ActivityNorm d k]
    (frontier : BalabanRGUniformLSIQuantitativeFrontier d N_c)
    (live : RGCauchyP81LiveTarget d N_c) :
    BalabanRGUniformLSIQuantitativeP81CanonicalLiveTargetBridge d N_c := by
  exact
    balaban_rg_uniform_lsi_quantitative_p81_interface_bridge_of_quantitative_frontier_and_live_target
      d N_c frontier live

/-- Projection back to the quantitative P81 interface bridge. -/
theorem quantitative_p81_interface_bridge_of_balaban_rg_uniform_lsi_quantitative_p81_canonical_live_target_bridge
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (bridge : BalabanRGUniformLSIQuantitativeP81CanonicalLiveTargetBridge d N_c) :
    BalabanRGUniformLSIQuantitativeP81InterfaceBridge d N_c := by
  exact bridge

/-- Projection back to the quantitative P81 kernel packet. -/
theorem quantitative_p81_kernel_packet_of_balaban_rg_uniform_lsi_quantitative_p81_canonical_live_target_bridge
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (bridge : BalabanRGUniformLSIQuantitativeP81CanonicalLiveTargetBridge d N_c) :
    BalabanRGUniformLSIQuantitativeP81KernelPacket d N_c := by
  exact
    quantitative_p81_kernel_packet_of_balaban_rg_uniform_lsi_quantitative_p81_interface_bridge bridge

/-- The canonical standard theorem-side live target reconstructed from the exact interface theorem. -/
theorem rg_cauchy_p81_canonical_live_target_of_balaban_rg_uniform_lsi_quantitative_p81_canonical_live_target_bridge
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (_bridge : BalabanRGUniformLSIQuantitativeP81CanonicalLiveTargetBridge d N_c) :
    RGCauchyP81LiveTarget d N_c := by
  exact rg_cauchy_p81_live_target_of_interface d N_c

/-- The canonical threshold-one witness for the standard theorem-side live target reconstructed
from the exact interface theorem. -/
theorem rg_cauchy_p81_canonical_threshold_one_of_balaban_rg_uniform_lsi_quantitative_p81_canonical_live_target_bridge
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (_bridge : BalabanRGUniformLSIQuantitativeP81CanonicalLiveTargetBridge d N_c) :
    0 < (1 : ℝ) ∧ ∀ β : ℝ, 1 ≤ β → RGIncrementDecayBound d N_c β := by
  refine ⟨one_pos, ?_⟩
  intro β hβ
  exact rg_increment_decay_P81 d N_c β hβ

/-- The theorem-side live target carried by the quantitative route agrees canonically with the
standard threshold-one live target reconstructed from the exact interface theorem. -/
theorem rg_cauchy_p81_carried_live_target_eq_canonical_of_balaban_rg_uniform_lsi_quantitative_p81_canonical_live_target_bridge
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (bridge : BalabanRGUniformLSIQuantitativeP81CanonicalLiveTargetBridge d N_c) :
    theorem_live_target_of_balaban_rg_uniform_lsi_quantitative_p81_kernel_packet
        (quantitative_p81_kernel_packet_of_balaban_rg_uniform_lsi_quantitative_p81_canonical_live_target_bridge bridge)
      =
      rg_cauchy_p81_canonical_live_target_of_balaban_rg_uniform_lsi_quantitative_p81_canonical_live_target_bridge bridge := by
  apply Subsingleton.elim

/-- Standard kernel output reconstructed from the canonical threshold-one theorem-side live target. -/
theorem rg_cauchy_p81_kernel_output_via_canonical_live_target_of_balaban_rg_uniform_lsi_quantitative_p81_canonical_live_target_bridge
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (bridge : BalabanRGUniformLSIQuantitativeP81CanonicalLiveTargetBridge d N_c) :
    RGCauchyP81KernelOutput d N_c := by
  exact
    rg_cauchy_p81_kernel_output_of_live_target d N_c
      (rg_cauchy_p81_canonical_live_target_of_balaban_rg_uniform_lsi_quantitative_p81_canonical_live_target_bridge bridge)

/-- Standard kernel input reconstructed from the canonical threshold-one theorem-side live target. -/
theorem rg_cauchy_p81_kernel_input_via_canonical_live_target_of_balaban_rg_uniform_lsi_quantitative_p81_canonical_live_target_bridge
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (bridge : BalabanRGUniformLSIQuantitativeP81CanonicalLiveTargetBridge d N_c) :
    RGCauchyP81KernelInput d N_c := by
  exact
    rg_cauchy_p81_kernel_input_of_live_target d N_c
      (rg_cauchy_p81_canonical_live_target_of_balaban_rg_uniform_lsi_quantitative_p81_canonical_live_target_bridge bridge)

/-- Standard obligation reconstructed from the canonical threshold-one theorem-side live target. -/
theorem rg_cauchy_p81_obligation_via_canonical_live_target_of_balaban_rg_uniform_lsi_quantitative_p81_canonical_live_target_bridge
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (bridge : BalabanRGUniformLSIQuantitativeP81CanonicalLiveTargetBridge d N_c) :
    RGCauchyP81Obligation d N_c := by
  exact
    rg_cauchy_p81_obligation_of_live_target d N_c
      (rg_cauchy_p81_canonical_live_target_of_balaban_rg_uniform_lsi_quantitative_p81_canonical_live_target_bridge bridge)

/-- Standard frontier reconstructed from the canonical threshold-one theorem-side live target
together with the standard audit packet attached to the quantitative route. -/
theorem rg_cauchy_p81_frontier_via_canonical_live_target_of_balaban_rg_uniform_lsi_quantitative_p81_canonical_live_target_bridge
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (bridge : BalabanRGUniformLSIQuantitativeP81CanonicalLiveTargetBridge d N_c) :
    RGCauchyP81Frontier d N_c := by
  exact
    rg_cauchy_p81_frontier_of_audit_packet_and_live_target d N_c
      (standard_audit_packet_of_balaban_rg_uniform_lsi_quantitative_p81_obstruction_coherence
        (quantitative_p81_obstruction_coherence_of_balaban_rg_uniform_lsi_quantitative_p81_kernel_packet
          (quantitative_p81_kernel_packet_of_balaban_rg_uniform_lsi_quantitative_p81_canonical_live_target_bridge bridge)))
      (rg_cauchy_p81_canonical_live_target_of_balaban_rg_uniform_lsi_quantitative_p81_canonical_live_target_bridge bridge)

/-- Standard coherence packet reconstructed from the canonical threshold-one theorem-side live
target together with the standard audit packet attached to the quantitative route. -/
theorem rg_cauchy_p81_coherence_packet_via_canonical_live_target_of_balaban_rg_uniform_lsi_quantitative_p81_canonical_live_target_bridge
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (bridge : BalabanRGUniformLSIQuantitativeP81CanonicalLiveTargetBridge d N_c) :
    RGCauchyP81CoherencePacket d N_c := by
  exact
    rg_cauchy_p81_coherence_packet_of_audit_packet_and_live_target d N_c
      (standard_audit_packet_of_balaban_rg_uniform_lsi_quantitative_p81_obstruction_coherence
        (quantitative_p81_obstruction_coherence_of_balaban_rg_uniform_lsi_quantitative_p81_kernel_packet
          (quantitative_p81_kernel_packet_of_balaban_rg_uniform_lsi_quantitative_p81_canonical_live_target_bridge bridge)))
      (rg_cauchy_p81_canonical_live_target_of_balaban_rg_uniform_lsi_quantitative_p81_canonical_live_target_bridge bridge)

/-- Bridge coherence: the kernel output carried by the quantitative route agrees canonically
with the one reconstructed from the canonical threshold-one theorem-side live target. -/
theorem rg_cauchy_p81_kernel_output_via_canonical_live_target_eq_canonical_of_balaban_rg_uniform_lsi_quantitative_p81_canonical_live_target_bridge
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (bridge : BalabanRGUniformLSIQuantitativeP81CanonicalLiveTargetBridge d N_c) :
    rg_cauchy_p81_kernel_output_of_balaban_rg_uniform_lsi_quantitative_p81_kernel_packet
        (quantitative_p81_kernel_packet_of_balaban_rg_uniform_lsi_quantitative_p81_canonical_live_target_bridge bridge)
      =
      rg_cauchy_p81_kernel_output_via_canonical_live_target_of_balaban_rg_uniform_lsi_quantitative_p81_canonical_live_target_bridge bridge := by
  apply Subsingleton.elim

/-- Bridge coherence: the kernel input carried by the quantitative route agrees canonically
with the one reconstructed from the canonical threshold-one theorem-side live target. -/
theorem rg_cauchy_p81_kernel_input_via_canonical_live_target_eq_canonical_of_balaban_rg_uniform_lsi_quantitative_p81_canonical_live_target_bridge
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (bridge : BalabanRGUniformLSIQuantitativeP81CanonicalLiveTargetBridge d N_c) :
    rg_cauchy_p81_kernel_input_of_balaban_rg_uniform_lsi_quantitative_p81_kernel_packet
        (quantitative_p81_kernel_packet_of_balaban_rg_uniform_lsi_quantitative_p81_canonical_live_target_bridge bridge)
      =
      rg_cauchy_p81_kernel_input_via_canonical_live_target_of_balaban_rg_uniform_lsi_quantitative_p81_canonical_live_target_bridge bridge := by
  apply Subsingleton.elim

/-- Bridge coherence: the obligation carried by the quantitative route agrees canonically with
the one reconstructed from the canonical threshold-one theorem-side live target. -/
theorem rg_cauchy_p81_obligation_via_canonical_live_target_eq_canonical_of_balaban_rg_uniform_lsi_quantitative_p81_canonical_live_target_bridge
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (bridge : BalabanRGUniformLSIQuantitativeP81CanonicalLiveTargetBridge d N_c) :
    obligation_of_balaban_rg_uniform_lsi_quantitative_p81_kernel_packet
        (quantitative_p81_kernel_packet_of_balaban_rg_uniform_lsi_quantitative_p81_canonical_live_target_bridge bridge)
      =
      rg_cauchy_p81_obligation_via_canonical_live_target_of_balaban_rg_uniform_lsi_quantitative_p81_canonical_live_target_bridge bridge := by
  apply Subsingleton.elim

/-- Bridge coherence: the frontier carried by the quantitative route agrees canonically with the
one reconstructed from the canonical threshold-one theorem-side live target. -/
theorem rg_cauchy_p81_frontier_via_canonical_live_target_eq_canonical_of_balaban_rg_uniform_lsi_quantitative_p81_canonical_live_target_bridge
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (bridge : BalabanRGUniformLSIQuantitativeP81CanonicalLiveTargetBridge d N_c) :
    rg_cauchy_p81_frontier_of_balaban_rg_uniform_lsi_quantitative_p81_kernel_packet
        (quantitative_p81_kernel_packet_of_balaban_rg_uniform_lsi_quantitative_p81_canonical_live_target_bridge bridge)
      =
      rg_cauchy_p81_frontier_via_canonical_live_target_of_balaban_rg_uniform_lsi_quantitative_p81_canonical_live_target_bridge bridge := by
  apply Subsingleton.elim

/-- Bridge coherence: the coherence packet carried by the quantitative route agrees canonically
with the one reconstructed from the canonical threshold-one theorem-side live target. -/
theorem rg_cauchy_p81_coherence_packet_via_canonical_live_target_eq_canonical_of_balaban_rg_uniform_lsi_quantitative_p81_canonical_live_target_bridge
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (bridge : BalabanRGUniformLSIQuantitativeP81CanonicalLiveTargetBridge d N_c) :
    rg_cauchy_p81_coherence_packet_of_balaban_rg_uniform_lsi_quantitative_p81_kernel_packet
        (quantitative_p81_kernel_packet_of_balaban_rg_uniform_lsi_quantitative_p81_canonical_live_target_bridge bridge)
      =
      rg_cauchy_p81_coherence_packet_via_canonical_live_target_of_balaban_rg_uniform_lsi_quantitative_p81_canonical_live_target_bridge bridge := by
  apply Subsingleton.elim

/-- Logical normal form: the canonical live-target bridge is equivalent to the quantitative P81
interface bridge. -/
theorem balaban_rg_uniform_lsi_quantitative_p81_canonical_live_target_bridge_iff_quantitative_p81_interface_bridge
    (d N_c : ℕ) [NeZero N_c] [∀ k, ActivityNorm d k] :
    BalabanRGUniformLSIQuantitativeP81CanonicalLiveTargetBridge d N_c ↔
      BalabanRGUniformLSIQuantitativeP81InterfaceBridge d N_c := by
  constructor
  · intro bridge
    exact bridge
  · intro bridge
    exact bridge

/-- Logical normal form: the canonical live-target bridge is equivalent to the pair consisting of
the direct quantitative frontier and the theorem-side live target. -/
theorem balaban_rg_uniform_lsi_quantitative_p81_canonical_live_target_bridge_iff_quantitative_frontier_and_live_target
    (d N_c : ℕ) [NeZero N_c] [∀ k, ActivityNorm d k] :
    BalabanRGUniformLSIQuantitativeP81CanonicalLiveTargetBridge d N_c ↔
      (BalabanRGUniformLSIQuantitativeFrontier d N_c ∧ RGCauchyP81LiveTarget d N_c) := by
  constructor
  · intro bridge
    exact
      ⟨ quantitative_frontier_of_balaban_rg_uniform_lsi_quantitative_p81_kernel_packet
            (quantitative_p81_kernel_packet_of_balaban_rg_uniform_lsi_quantitative_p81_canonical_live_target_bridge bridge),
        theorem_live_target_of_balaban_rg_uniform_lsi_quantitative_p81_kernel_packet
            (quantitative_p81_kernel_packet_of_balaban_rg_uniform_lsi_quantitative_p81_canonical_live_target_bridge bridge) ⟩
  · intro h
    exact
      balaban_rg_uniform_lsi_quantitative_p81_canonical_live_target_bridge_of_quantitative_frontier_and_live_target
        d N_c h.1 h.2

end

end YangMills.ClayCore
