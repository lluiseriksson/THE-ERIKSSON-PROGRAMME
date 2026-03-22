import Mathlib
import YangMills.ClayCore.BalabanRG.BalabanRGUniformLSIQuantitativeP81ThresholdOneObstructionCoherence

namespace YangMills.ClayCore

open scoped BigOperators
open Classical
noncomputable section

/-- Dedicated coherence hub centralizing the explicit threshold-one (`β = 1`) packet together
with the threshold-one obstruction coherence hub and the standard chosen-beta/kernel corridor. -/
structure BalabanRGUniformLSIQuantitativeP81ThresholdOneKernelCoherence
    (d N_c : ℕ) [NeZero N_c] [∀ k, ActivityNorm d k] : Prop where
  thresholdOneObstructionCoherence :
    BalabanRGUniformLSIQuantitativeP81ThresholdOneObstructionCoherence d N_c
  thresholdOneObstructionPacket :
    BalabanRGUniformLSIQuantitativeP81ThresholdOneObstructionPacket d N_c
  thresholdOnePacket :
    BalabanRGUniformLSIQuantitativeP81ThresholdOnePacket d N_c
  quantitativeP81KernelPacket :
    BalabanRGUniformLSIQuantitativeP81KernelPacket d N_c
  quantitativeP81ChosenBetaPacket :
    BalabanRGUniformLSIQuantitativeP81ChosenBetaPacket d N_c
  quantitativeP81WitnessPacket :
    BalabanRGUniformLSIQuantitativeP81WitnessPacket d N_c
  quantitativeP81ObstructionCoherence :
    BalabanRGUniformLSIQuantitativeP81ObstructionCoherence d N_c
  quantitativeP81ObstructionPacket :
    BalabanRGUniformLSIQuantitativeP81ObstructionPacket d N_c
  quantitativeP81Coherence :
    BalabanRGUniformLSIQuantitativeP81Coherence d N_c
  quantitativeP81Packet :
    BalabanRGUniformLSIQuantitativeP81Packet d N_c
  quantitativeFrontier :
    BalabanRGUniformLSIQuantitativeFrontier d N_c
  theoremLiveTarget :
    RGCauchyP81LiveTarget d N_c
  p81Frontier :
    RGCauchyP81Frontier d N_c
  p81CoherencePacket :
    RGCauchyP81CoherencePacket d N_c
  kernelOutput :
    RGCauchyP81KernelOutput d N_c
  kernelInput :
    RGCauchyP81KernelInput d N_c
  obligation :
    RGCauchyP81Obligation d N_c
  thresholdOneChosenBetaWitness :
    ∃ β : ℝ, 1 ≤ β ∧ RGIncrementDecayBound d N_c β ∧ RGCauchySummabilityBound d N_c β
  standardChosenBetaWitness :
    ∃ β : ℝ, 1 ≤ β ∧ RGIncrementDecayBound d N_c β ∧ RGCauchySummabilityBound d N_c β

/-- Canonical threshold-one kernel coherence hub from the threshold-one obstruction coherence hub. -/
theorem balaban_rg_uniform_lsi_quantitative_p81_threshold_one_kernel_coherence_of_threshold_one_obstruction_coherence
    (d N_c : ℕ) [NeZero N_c] [∀ k, ActivityNorm d k]
    (coh : BalabanRGUniformLSIQuantitativeP81ThresholdOneObstructionCoherence d N_c) :
    BalabanRGUniformLSIQuantitativeP81ThresholdOneKernelCoherence d N_c := by
  let packet₀ : BalabanRGUniformLSIQuantitativeP81ThresholdOnePacket d N_c :=
    threshold_one_packet_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_obstruction_coherence
      coh
  let kernelPacket : BalabanRGUniformLSIQuantitativeP81KernelPacket d N_c :=
    coh.quantitativeP81KernelPacket
  let chosenPacket : BalabanRGUniformLSIQuantitativeP81ChosenBetaPacket d N_c :=
    quantitative_p81_chosen_beta_packet_of_balaban_rg_uniform_lsi_quantitative_p81_kernel_packet
      kernelPacket
  let witnessPacket : BalabanRGUniformLSIQuantitativeP81WitnessPacket d N_c :=
    quantitative_p81_witness_packet_of_balaban_rg_uniform_lsi_quantitative_p81_kernel_packet
      kernelPacket
  exact
    ⟨ coh,
      threshold_one_obstruction_packet_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_obstruction_coherence
        coh,
      packet₀,
      kernelPacket,
      chosenPacket,
      witnessPacket,
      quantitative_p81_obstruction_coherence_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_obstruction_coherence
        coh,
      quantitative_p81_obstruction_packet_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_obstruction_coherence
        coh,
      coh.quantitativeP81Coherence,
      coh.quantitativeP81Packet,
      coh.quantitativeFrontier,
      coh.theoremLiveTarget,
      coh.p81Frontier,
      coh.p81CoherencePacket,
      coh.kernelOutput,
      coh.kernelInput,
      coh.obligation,
      ⟨ 1,
        le_rfl,
        rg_increment_decay_P81_at_one_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_packet
          packet₀,
        rg_cauchy_from_increment_decay_at_one_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_packet
          packet₀ ⟩,
      chosen_beta_witness_of_balaban_rg_uniform_lsi_quantitative_p81_kernel_packet
        kernelPacket ⟩

/-- Canonical threshold-one kernel coherence hub from the direct quantitative frontier together
with the theorem-side live target. -/
theorem balaban_rg_uniform_lsi_quantitative_p81_threshold_one_kernel_coherence_of_quantitative_frontier_and_live_target
    (d N_c : ℕ) [NeZero N_c] [∀ k, ActivityNorm d k]
    (frontier : BalabanRGUniformLSIQuantitativeFrontier d N_c)
    (live : RGCauchyP81LiveTarget d N_c) :
    BalabanRGUniformLSIQuantitativeP81ThresholdOneKernelCoherence d N_c := by
  exact
    balaban_rg_uniform_lsi_quantitative_p81_threshold_one_kernel_coherence_of_threshold_one_obstruction_coherence
      d N_c
      (balaban_rg_uniform_lsi_quantitative_p81_threshold_one_obstruction_coherence_of_quantitative_frontier_and_live_target
        d N_c frontier live)

/-- Projection to the threshold-one obstruction coherence hub. -/
theorem threshold_one_obstruction_coherence_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_kernel_coherence
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (coh : BalabanRGUniformLSIQuantitativeP81ThresholdOneKernelCoherence d N_c) :
    BalabanRGUniformLSIQuantitativeP81ThresholdOneObstructionCoherence d N_c := by
  exact coh.thresholdOneObstructionCoherence

/-- Projection to the explicit threshold-one obstruction packet. -/
theorem threshold_one_obstruction_packet_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_kernel_coherence
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (coh : BalabanRGUniformLSIQuantitativeP81ThresholdOneKernelCoherence d N_c) :
    BalabanRGUniformLSIQuantitativeP81ThresholdOneObstructionPacket d N_c := by
  exact coh.thresholdOneObstructionPacket

/-- Projection to the explicit threshold-one packet. -/
theorem threshold_one_packet_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_kernel_coherence
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (coh : BalabanRGUniformLSIQuantitativeP81ThresholdOneKernelCoherence d N_c) :
    BalabanRGUniformLSIQuantitativeP81ThresholdOnePacket d N_c := by
  exact coh.thresholdOnePacket

/-- Projection to the standard quantitative P81 kernel packet. -/
theorem quantitative_p81_kernel_packet_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_kernel_coherence
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (coh : BalabanRGUniformLSIQuantitativeP81ThresholdOneKernelCoherence d N_c) :
    BalabanRGUniformLSIQuantitativeP81KernelPacket d N_c := by
  exact coh.quantitativeP81KernelPacket

/-- Projection to the standard chosen-beta packet. -/
theorem quantitative_p81_chosen_beta_packet_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_kernel_coherence
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (coh : BalabanRGUniformLSIQuantitativeP81ThresholdOneKernelCoherence d N_c) :
    BalabanRGUniformLSIQuantitativeP81ChosenBetaPacket d N_c := by
  exact coh.quantitativeP81ChosenBetaPacket

/-- Projection to the standard witness packet. -/
theorem quantitative_p81_witness_packet_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_kernel_coherence
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (coh : BalabanRGUniformLSIQuantitativeP81ThresholdOneKernelCoherence d N_c) :
    BalabanRGUniformLSIQuantitativeP81WitnessPacket d N_c := by
  exact coh.quantitativeP81WitnessPacket

/-- Projection to the explicit threshold-one chosen-beta witness at `β = 1`. -/
theorem threshold_one_chosen_beta_witness_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_kernel_coherence
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (coh : BalabanRGUniformLSIQuantitativeP81ThresholdOneKernelCoherence d N_c) :
    ∃ β : ℝ, 1 ≤ β ∧ RGIncrementDecayBound d N_c β ∧ RGCauchySummabilityBound d N_c β := by
  exact coh.thresholdOneChosenBetaWitness

/-- Projection to the standard chosen-beta witness carried by the standard kernel packet. -/
theorem standard_chosen_beta_witness_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_kernel_coherence
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (coh : BalabanRGUniformLSIQuantitativeP81ThresholdOneKernelCoherence d N_c) :
    ∃ β : ℝ, 1 ≤ β ∧ RGIncrementDecayBound d N_c β ∧ RGCauchySummabilityBound d N_c β := by
  exact coh.standardChosenBetaWitness

/-- Projection to the theorem-side live target. -/
theorem theorem_live_target_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_kernel_coherence
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (coh : BalabanRGUniformLSIQuantitativeP81ThresholdOneKernelCoherence d N_c) :
    RGCauchyP81LiveTarget d N_c := by
  exact coh.theoremLiveTarget

/-- Projection to the short public P81 frontier. -/
theorem rg_cauchy_p81_frontier_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_kernel_coherence
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (coh : BalabanRGUniformLSIQuantitativeP81ThresholdOneKernelCoherence d N_c) :
    RGCauchyP81Frontier d N_c := by
  exact coh.p81Frontier

/-- Projection to the theorem-side coherence packet. -/
theorem rg_cauchy_p81_coherence_packet_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_kernel_coherence
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (coh : BalabanRGUniformLSIQuantitativeP81ThresholdOneKernelCoherence d N_c) :
    RGCauchyP81CoherencePacket d N_c := by
  exact coh.p81CoherencePacket

/-- Projection to the kernel output. -/
theorem rg_cauchy_p81_kernel_output_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_kernel_coherence
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (coh : BalabanRGUniformLSIQuantitativeP81ThresholdOneKernelCoherence d N_c) :
    RGCauchyP81KernelOutput d N_c := by
  exact coh.kernelOutput

/-- Projection to the kernel input. -/
theorem rg_cauchy_p81_kernel_input_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_kernel_coherence
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (coh : BalabanRGUniformLSIQuantitativeP81ThresholdOneKernelCoherence d N_c) :
    RGCauchyP81KernelInput d N_c := by
  exact coh.kernelInput

/-- Projection to the obligation surface. -/
theorem obligation_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_kernel_coherence
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (coh : BalabanRGUniformLSIQuantitativeP81ThresholdOneKernelCoherence d N_c) :
    RGCauchyP81Obligation d N_c := by
  exact coh.obligation

/-- Kernel coherence: the standard chosen-beta witness agrees canonically with the explicit
threshold-one chosen-beta witness at `β = 1`. -/
theorem chosen_beta_witness_eq_threshold_one_canonical_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_kernel_coherence
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (coh : BalabanRGUniformLSIQuantitativeP81ThresholdOneKernelCoherence d N_c) :
    standard_chosen_beta_witness_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_kernel_coherence
        coh
      =
    threshold_one_chosen_beta_witness_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_kernel_coherence
        coh := by
  apply Subsingleton.elim

/-- Kernel coherence: the theorem-side live target inside the standard kernel packet agrees
canonically with the explicit threshold-one theorem-side live target. -/
theorem theorem_live_target_eq_threshold_one_canonical_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_kernel_coherence
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (coh : BalabanRGUniformLSIQuantitativeP81ThresholdOneKernelCoherence d N_c) :
    theorem_live_target_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_kernel_coherence
        coh
      =
    rg_cauchy_p81_threshold_one_live_target_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_packet
      (threshold_one_packet_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_kernel_coherence
        coh) := by
  apply Subsingleton.elim

/-- Kernel coherence: the short public P81 frontier inside the standard kernel packet agrees
canonically with the explicit threshold-one frontier. -/
theorem rg_cauchy_p81_frontier_eq_threshold_one_canonical_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_kernel_coherence
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (coh : BalabanRGUniformLSIQuantitativeP81ThresholdOneKernelCoherence d N_c) :
    rg_cauchy_p81_frontier_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_kernel_coherence
        coh
      =
    rg_cauchy_p81_frontier_at_one_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_packet
      (threshold_one_packet_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_kernel_coherence
        coh) := by
  apply Subsingleton.elim

/-- Kernel coherence: the theorem-side coherence packet inside the standard kernel packet agrees
canonically with the explicit threshold-one coherence packet. -/
theorem rg_cauchy_p81_coherence_packet_eq_threshold_one_canonical_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_kernel_coherence
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (coh : BalabanRGUniformLSIQuantitativeP81ThresholdOneKernelCoherence d N_c) :
    rg_cauchy_p81_coherence_packet_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_kernel_coherence
        coh
      =
    rg_cauchy_p81_coherence_packet_at_one_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_packet
      (threshold_one_packet_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_kernel_coherence
        coh) := by
  apply Subsingleton.elim

/-- Kernel coherence: the kernel output inside the standard kernel packet agrees canonically
with the explicit threshold-one kernel output. -/
theorem kernel_output_eq_threshold_one_canonical_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_kernel_coherence
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (coh : BalabanRGUniformLSIQuantitativeP81ThresholdOneKernelCoherence d N_c) :
    rg_cauchy_p81_kernel_output_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_kernel_coherence
        coh
      =
    rg_cauchy_p81_kernel_output_at_one_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_packet
      (threshold_one_packet_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_kernel_coherence
        coh) := by
  apply Subsingleton.elim

/-- Kernel coherence: the kernel input inside the standard kernel packet agrees canonically
with the explicit threshold-one kernel input. -/
theorem kernel_input_eq_threshold_one_canonical_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_kernel_coherence
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (coh : BalabanRGUniformLSIQuantitativeP81ThresholdOneKernelCoherence d N_c) :
    rg_cauchy_p81_kernel_input_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_kernel_coherence
        coh
      =
    rg_cauchy_p81_kernel_input_at_one_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_packet
      (threshold_one_packet_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_kernel_coherence
        coh) := by
  apply Subsingleton.elim

/-- Kernel coherence: the obligation surface inside the standard kernel packet agrees canonically
with the explicit threshold-one obligation. -/
theorem obligation_eq_threshold_one_canonical_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_kernel_coherence
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (coh : BalabanRGUniformLSIQuantitativeP81ThresholdOneKernelCoherence d N_c) :
    obligation_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_kernel_coherence
        coh
      =
    rg_cauchy_p81_obligation_at_one_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_packet
      (threshold_one_packet_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_kernel_coherence
        coh) := by
  apply Subsingleton.elim

/-- Logical normal form: the threshold-one kernel coherence hub is equivalent to the
threshold-one obstruction coherence hub. -/
theorem balaban_rg_uniform_lsi_quantitative_p81_threshold_one_kernel_coherence_iff_threshold_one_obstruction_coherence
    (d N_c : ℕ) [NeZero N_c] [∀ k, ActivityNorm d k] :
    BalabanRGUniformLSIQuantitativeP81ThresholdOneKernelCoherence d N_c ↔
      BalabanRGUniformLSIQuantitativeP81ThresholdOneObstructionCoherence d N_c := by
  constructor
  · intro coh
    exact
      threshold_one_obstruction_coherence_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_kernel_coherence
        coh
  · intro coh
    exact
      balaban_rg_uniform_lsi_quantitative_p81_threshold_one_kernel_coherence_of_threshold_one_obstruction_coherence
        d N_c coh

/-- Logical normal form: the threshold-one kernel coherence hub is equivalent to the pair
consisting of the direct quantitative frontier and the theorem-side live target. -/
theorem balaban_rg_uniform_lsi_quantitative_p81_threshold_one_kernel_coherence_iff_quantitative_frontier_and_live_target
    (d N_c : ℕ) [NeZero N_c] [∀ k, ActivityNorm d k] :
    BalabanRGUniformLSIQuantitativeP81ThresholdOneKernelCoherence d N_c ↔
      (BalabanRGUniformLSIQuantitativeFrontier d N_c ∧ RGCauchyP81LiveTarget d N_c) := by
  constructor
  · intro coh
    exact ⟨coh.quantitativeFrontier, coh.theoremLiveTarget⟩
  · intro h
    exact
      balaban_rg_uniform_lsi_quantitative_p81_threshold_one_kernel_coherence_of_quantitative_frontier_and_live_target
        d N_c h.1 h.2

end

end YangMills.ClayCore
