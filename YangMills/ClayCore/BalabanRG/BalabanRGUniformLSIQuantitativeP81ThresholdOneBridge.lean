import Mathlib
import YangMills.ClayCore.BalabanRG.BalabanRGUniformLSIQuantitativeP81CanonicalLiveTargetBridge

namespace YangMills.ClayCore

open scoped BigOperators
open Classical
noncomputable section

/-- Bridge from the quantitative theorem-side canonical live-target route to the explicit
threshold-one (`β = 1`) specialization of the exact interface theorem. -/
def BalabanRGUniformLSIQuantitativeP81ThresholdOneBridge
    (d N_c : ℕ) [NeZero N_c] [∀ k, ActivityNorm d k] : Prop :=
  BalabanRGUniformLSIQuantitativeP81CanonicalLiveTargetBridge d N_c

/-- Canonical bridge from the quantitative P81 canonical live-target bridge. -/
theorem balaban_rg_uniform_lsi_quantitative_p81_threshold_one_bridge_of_quantitative_p81_canonical_live_target_bridge
    (d N_c : ℕ) [NeZero N_c] [∀ k, ActivityNorm d k]
    (bridge : BalabanRGUniformLSIQuantitativeP81CanonicalLiveTargetBridge d N_c) :
    BalabanRGUniformLSIQuantitativeP81ThresholdOneBridge d N_c := by
  exact bridge

/-- Canonical bridge from the direct quantitative frontier together with the theorem-side live
target. -/
theorem balaban_rg_uniform_lsi_quantitative_p81_threshold_one_bridge_of_quantitative_frontier_and_live_target
    (d N_c : ℕ) [NeZero N_c] [∀ k, ActivityNorm d k]
    (frontier : BalabanRGUniformLSIQuantitativeFrontier d N_c)
    (live : RGCauchyP81LiveTarget d N_c) :
    BalabanRGUniformLSIQuantitativeP81ThresholdOneBridge d N_c := by
  exact
    balaban_rg_uniform_lsi_quantitative_p81_canonical_live_target_bridge_of_quantitative_frontier_and_live_target
      d N_c frontier live

/-- Projection back to the quantitative P81 canonical live-target bridge. -/
theorem quantitative_p81_canonical_live_target_bridge_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_bridge
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (bridge : BalabanRGUniformLSIQuantitativeP81ThresholdOneBridge d N_c) :
    BalabanRGUniformLSIQuantitativeP81CanonicalLiveTargetBridge d N_c := by
  exact bridge

/-- Projection back to the quantitative P81 interface bridge. -/
theorem quantitative_p81_interface_bridge_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_bridge
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (bridge : BalabanRGUniformLSIQuantitativeP81ThresholdOneBridge d N_c) :
    BalabanRGUniformLSIQuantitativeP81InterfaceBridge d N_c := by
  exact
    quantitative_p81_interface_bridge_of_balaban_rg_uniform_lsi_quantitative_p81_canonical_live_target_bridge
      (quantitative_p81_canonical_live_target_bridge_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_bridge bridge)

/-- Projection back to the quantitative P81 kernel packet. -/
theorem quantitative_p81_kernel_packet_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_bridge
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (bridge : BalabanRGUniformLSIQuantitativeP81ThresholdOneBridge d N_c) :
    BalabanRGUniformLSIQuantitativeP81KernelPacket d N_c := by
  exact
    quantitative_p81_kernel_packet_of_balaban_rg_uniform_lsi_quantitative_p81_canonical_live_target_bridge
      (quantitative_p81_canonical_live_target_bridge_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_bridge bridge)

/-- Exact interface theorem specialized to the explicit threshold-one case `β = 1`. -/
theorem rg_increment_decay_P81_at_one_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_bridge
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (_bridge : BalabanRGUniformLSIQuantitativeP81ThresholdOneBridge d N_c) :
    RGIncrementDecayBound d N_c 1 := by
  exact rg_increment_decay_P81 d N_c 1 le_rfl

/-- Exact derived summability theorem specialized to the explicit threshold-one case `β = 1`. -/
theorem rg_cauchy_from_increment_decay_at_one_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_bridge
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (_bridge : BalabanRGUniformLSIQuantitativeP81ThresholdOneBridge d N_c) :
    RGCauchySummabilityBound d N_c 1 := by
  exact rg_cauchy_from_increment_decay d N_c 1 le_rfl

/-- The canonical threshold-one theorem-side live target reconstructed from the exact interface
theorem. -/
theorem rg_cauchy_p81_threshold_one_live_target_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_bridge
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (bridge : BalabanRGUniformLSIQuantitativeP81ThresholdOneBridge d N_c) :
    RGCauchyP81LiveTarget d N_c := by
  exact
    rg_cauchy_p81_canonical_live_target_of_balaban_rg_uniform_lsi_quantitative_p81_canonical_live_target_bridge
      (quantitative_p81_canonical_live_target_bridge_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_bridge bridge)

/-- Canonical threshold-one kernel output reconstructed from the threshold-one theorem-side live
target. -/
theorem rg_cauchy_p81_kernel_output_at_one_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_bridge
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (bridge : BalabanRGUniformLSIQuantitativeP81ThresholdOneBridge d N_c) :
    RGCauchyP81KernelOutput d N_c := by
  exact
    rg_cauchy_p81_kernel_output_via_canonical_live_target_of_balaban_rg_uniform_lsi_quantitative_p81_canonical_live_target_bridge
      (quantitative_p81_canonical_live_target_bridge_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_bridge bridge)

/-- Canonical threshold-one kernel input reconstructed from the threshold-one theorem-side live
target. -/
theorem rg_cauchy_p81_kernel_input_at_one_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_bridge
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (bridge : BalabanRGUniformLSIQuantitativeP81ThresholdOneBridge d N_c) :
    RGCauchyP81KernelInput d N_c := by
  exact
    rg_cauchy_p81_kernel_input_via_canonical_live_target_of_balaban_rg_uniform_lsi_quantitative_p81_canonical_live_target_bridge
      (quantitative_p81_canonical_live_target_bridge_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_bridge bridge)

/-- Canonical threshold-one obligation reconstructed from the threshold-one theorem-side live
target. -/
theorem rg_cauchy_p81_obligation_at_one_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_bridge
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (bridge : BalabanRGUniformLSIQuantitativeP81ThresholdOneBridge d N_c) :
    RGCauchyP81Obligation d N_c := by
  exact
    rg_cauchy_p81_obligation_via_canonical_live_target_of_balaban_rg_uniform_lsi_quantitative_p81_canonical_live_target_bridge
      (quantitative_p81_canonical_live_target_bridge_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_bridge bridge)

/-- Bridge coherence: the explicit threshold-one increment-decay statement agrees canonically
with the direct threshold-one witness reconstructed from the canonical live-target bridge. -/
theorem rg_increment_decay_P81_at_one_eq_canonical_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_bridge
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (bridge : BalabanRGUniformLSIQuantitativeP81ThresholdOneBridge d N_c) :
    rg_increment_decay_P81_at_one_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_bridge bridge =
      (rg_cauchy_p81_canonical_threshold_one_of_balaban_rg_uniform_lsi_quantitative_p81_canonical_live_target_bridge
        (quantitative_p81_canonical_live_target_bridge_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_bridge bridge)).2 1 le_rfl := by
  apply Subsingleton.elim

/-- Bridge coherence: the explicit threshold-one summability statement agrees canonically
with the direct threshold-one summability theorem. -/
theorem rg_cauchy_from_increment_decay_at_one_eq_canonical_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_bridge
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (bridge : BalabanRGUniformLSIQuantitativeP81ThresholdOneBridge d N_c) :
    rg_cauchy_from_increment_decay_at_one_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_bridge bridge =
      rg_cauchy_from_increment_decay d N_c 1 le_rfl := by
  apply Subsingleton.elim

/-- Bridge coherence: the theorem-side live target carried by the quantitative route agrees
canonically with the explicit threshold-one live target. -/
theorem rg_cauchy_p81_carried_live_target_eq_threshold_one_canonical_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_bridge
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (bridge : BalabanRGUniformLSIQuantitativeP81ThresholdOneBridge d N_c) :
    theorem_live_target_of_balaban_rg_uniform_lsi_quantitative_p81_kernel_packet
        (quantitative_p81_kernel_packet_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_bridge bridge)
      =
      rg_cauchy_p81_threshold_one_live_target_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_bridge bridge := by
  exact
    rg_cauchy_p81_carried_live_target_eq_canonical_of_balaban_rg_uniform_lsi_quantitative_p81_canonical_live_target_bridge
      (quantitative_p81_canonical_live_target_bridge_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_bridge bridge)

/-- Bridge coherence: the kernel output carried by the quantitative route agrees canonically
with the explicit threshold-one kernel output. -/
theorem rg_cauchy_p81_kernel_output_at_one_eq_canonical_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_bridge
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (bridge : BalabanRGUniformLSIQuantitativeP81ThresholdOneBridge d N_c) :
    rg_cauchy_p81_kernel_output_of_balaban_rg_uniform_lsi_quantitative_p81_kernel_packet
        (quantitative_p81_kernel_packet_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_bridge bridge)
      =
      rg_cauchy_p81_kernel_output_at_one_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_bridge bridge := by
  exact
    rg_cauchy_p81_kernel_output_via_canonical_live_target_eq_canonical_of_balaban_rg_uniform_lsi_quantitative_p81_canonical_live_target_bridge
      (quantitative_p81_canonical_live_target_bridge_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_bridge bridge)

/-- Bridge coherence: the kernel input carried by the quantitative route agrees canonically
with the explicit threshold-one kernel input. -/
theorem rg_cauchy_p81_kernel_input_at_one_eq_canonical_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_bridge
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (bridge : BalabanRGUniformLSIQuantitativeP81ThresholdOneBridge d N_c) :
    rg_cauchy_p81_kernel_input_of_balaban_rg_uniform_lsi_quantitative_p81_kernel_packet
        (quantitative_p81_kernel_packet_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_bridge bridge)
      =
      rg_cauchy_p81_kernel_input_at_one_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_bridge bridge := by
  exact
    rg_cauchy_p81_kernel_input_via_canonical_live_target_eq_canonical_of_balaban_rg_uniform_lsi_quantitative_p81_canonical_live_target_bridge
      (quantitative_p81_canonical_live_target_bridge_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_bridge bridge)

/-- Bridge coherence: the obligation carried by the quantitative route agrees canonically with
the explicit threshold-one obligation. -/
theorem rg_cauchy_p81_obligation_at_one_eq_canonical_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_bridge
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (bridge : BalabanRGUniformLSIQuantitativeP81ThresholdOneBridge d N_c) :
    obligation_of_balaban_rg_uniform_lsi_quantitative_p81_kernel_packet
        (quantitative_p81_kernel_packet_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_bridge bridge)
      =
      rg_cauchy_p81_obligation_at_one_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_bridge bridge := by
  exact
    rg_cauchy_p81_obligation_via_canonical_live_target_eq_canonical_of_balaban_rg_uniform_lsi_quantitative_p81_canonical_live_target_bridge
      (quantitative_p81_canonical_live_target_bridge_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_bridge bridge)

/-- Logical normal form: the threshold-one bridge is equivalent to the quantitative P81
canonical live-target bridge. -/
theorem balaban_rg_uniform_lsi_quantitative_p81_threshold_one_bridge_iff_quantitative_p81_canonical_live_target_bridge
    (d N_c : ℕ) [NeZero N_c] [∀ k, ActivityNorm d k] :
    BalabanRGUniformLSIQuantitativeP81ThresholdOneBridge d N_c ↔
      BalabanRGUniformLSIQuantitativeP81CanonicalLiveTargetBridge d N_c := by
  constructor
  · intro bridge
    exact bridge
  · intro bridge
    exact bridge

/-- Logical normal form: the threshold-one bridge is equivalent to the pair consisting of the
direct quantitative frontier and the theorem-side live target. -/
theorem balaban_rg_uniform_lsi_quantitative_p81_threshold_one_bridge_iff_quantitative_frontier_and_live_target
    (d N_c : ℕ) [NeZero N_c] [∀ k, ActivityNorm d k] :
    BalabanRGUniformLSIQuantitativeP81ThresholdOneBridge d N_c ↔
      (BalabanRGUniformLSIQuantitativeFrontier d N_c ∧ RGCauchyP81LiveTarget d N_c) := by
  constructor
  · intro bridge
    exact
      ⟨ quantitative_frontier_of_balaban_rg_uniform_lsi_quantitative_p81_kernel_packet
            (quantitative_p81_kernel_packet_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_bridge bridge),
        theorem_live_target_of_balaban_rg_uniform_lsi_quantitative_p81_kernel_packet
            (quantitative_p81_kernel_packet_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_bridge bridge) ⟩
  · intro h
    exact
      balaban_rg_uniform_lsi_quantitative_p81_threshold_one_bridge_of_quantitative_frontier_and_live_target
        d N_c h.1 h.2

end

end YangMills.ClayCore
