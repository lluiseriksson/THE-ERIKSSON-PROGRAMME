import Mathlib
import YangMills.ClayCore.BalabanRG.BalabanRGUniformLSIQuantitativeP81ChosenBetaPacket

namespace YangMills.ClayCore

open scoped BigOperators
open Classical
noncomputable section

/-- Direct theorem-side kernel corridor packet for the quantitative P81 route.
It packages the canonical chosen-β surface together with the corresponding
`kernelOutput`, `kernelInput`, and `obligation` objects. -/
structure BalabanRGUniformLSIQuantitativeP81KernelPacket
    (d N_c : ℕ) [NeZero N_c] [∀ k, ActivityNorm d k] : Prop where
  quantitativeP81ChosenBetaPacket : BalabanRGUniformLSIQuantitativeP81ChosenBetaPacket d N_c
  quantitativeP81WitnessPacket : BalabanRGUniformLSIQuantitativeP81WitnessPacket d N_c
  quantitativeP81ObstructionCoherence : BalabanRGUniformLSIQuantitativeP81ObstructionCoherence d N_c
  quantitativeP81ObstructionPacket : BalabanRGUniformLSIQuantitativeP81ObstructionPacket d N_c
  quantitativeP81Coherence : BalabanRGUniformLSIQuantitativeP81Coherence d N_c
  quantitativeP81Packet : BalabanRGUniformLSIQuantitativeP81Packet d N_c
  quantitativeFrontier : BalabanRGUniformLSIQuantitativeFrontier d N_c
  theoremLiveTarget : RGCauchyP81LiveTarget d N_c
  p81Frontier : RGCauchyP81Frontier d N_c
  p81CoherencePacket : RGCauchyP81CoherencePacket d N_c
  kernelOutput : RGCauchyP81KernelOutput d N_c
  kernelInput : RGCauchyP81KernelInput d N_c
  obligation : RGCauchyP81Obligation d N_c
  chosenBetaWitness : ∃ β : ℝ, 1 ≤ β ∧ RGIncrementDecayBound d N_c β ∧ RGCauchySummabilityBound d N_c β

/-- Canonical quantitative P81 kernel packet from the chosen-beta theorem-side packet. -/
theorem balaban_rg_uniform_lsi_quantitative_p81_kernel_packet_of_quantitative_p81_chosen_beta_packet
    (d N_c : ℕ) [NeZero N_c] [∀ k, ActivityNorm d k]
    (packet : BalabanRGUniformLSIQuantitativeP81ChosenBetaPacket d N_c) :
    BalabanRGUniformLSIQuantitativeP81KernelPacket d N_c := by
  let hβ :
      ∃ β : ℝ, 1 ≤ β ∧ RGIncrementDecayBound d N_c β ∧ RGCauchySummabilityBound d N_c β :=
    chosen_beta_witness_of_balaban_rg_uniform_lsi_quantitative_p81_chosen_beta_packet packet
  let output : RGCauchyP81KernelOutput d N_c := ⟨hβ⟩
  exact
    ⟨ packet,
      quantitative_p81_witness_packet_of_balaban_rg_uniform_lsi_quantitative_p81_chosen_beta_packet packet,
      quantitative_p81_obstruction_coherence_of_balaban_rg_uniform_lsi_quantitative_p81_chosen_beta_packet packet,
      quantitative_p81_obstruction_packet_of_balaban_rg_uniform_lsi_quantitative_p81_chosen_beta_packet packet,
      quantitative_p81_coherence_of_balaban_rg_uniform_lsi_quantitative_p81_chosen_beta_packet packet,
      quantitative_p81_packet_of_balaban_rg_uniform_lsi_quantitative_p81_chosen_beta_packet packet,
      quantitative_frontier_of_balaban_rg_uniform_lsi_quantitative_p81_chosen_beta_packet packet,
      theorem_live_target_of_balaban_rg_uniform_lsi_quantitative_p81_chosen_beta_packet packet,
      rg_cauchy_p81_frontier_of_balaban_rg_uniform_lsi_quantitative_p81_chosen_beta_packet packet,
      rg_cauchy_p81_coherence_packet_of_balaban_rg_uniform_lsi_quantitative_p81_chosen_beta_packet packet,
      output,
      rg_cauchy_p81_kernel_input_of_output d N_c output,
      rg_cauchy_p81_obligation_of_output d N_c output,
      hβ ⟩

/-- Canonical quantitative P81 kernel packet from the direct quantitative frontier together with
the theorem-side live target. -/
theorem balaban_rg_uniform_lsi_quantitative_p81_kernel_packet_of_quantitative_frontier_and_live_target
    (d N_c : ℕ) [NeZero N_c] [∀ k, ActivityNorm d k]
    (frontier : BalabanRGUniformLSIQuantitativeFrontier d N_c)
    (live : RGCauchyP81LiveTarget d N_c) :
    BalabanRGUniformLSIQuantitativeP81KernelPacket d N_c := by
  exact
    balaban_rg_uniform_lsi_quantitative_p81_kernel_packet_of_quantitative_p81_chosen_beta_packet d N_c
      (balaban_rg_uniform_lsi_quantitative_p81_chosen_beta_packet_of_quantitative_frontier_and_live_target
        d N_c frontier live)

/-- Canonical quantitative P81 kernel packet from the witness-selected theorem-side packet. -/
theorem balaban_rg_uniform_lsi_quantitative_p81_kernel_packet_of_quantitative_p81_witness_packet
    (d N_c : ℕ) [NeZero N_c] [∀ k, ActivityNorm d k]
    (packet : BalabanRGUniformLSIQuantitativeP81WitnessPacket d N_c) :
    BalabanRGUniformLSIQuantitativeP81KernelPacket d N_c := by
  exact
    balaban_rg_uniform_lsi_quantitative_p81_kernel_packet_of_quantitative_p81_chosen_beta_packet d N_c
      (balaban_rg_uniform_lsi_quantitative_p81_chosen_beta_packet_of_quantitative_p81_witness_packet
        d N_c packet)

/-- Canonical quantitative P81 kernel packet from the quantitative obstruction coherence hub. -/
theorem balaban_rg_uniform_lsi_quantitative_p81_kernel_packet_of_quantitative_p81_obstruction_coherence
    (d N_c : ℕ) [NeZero N_c] [∀ k, ActivityNorm d k]
    (coh : BalabanRGUniformLSIQuantitativeP81ObstructionCoherence d N_c) :
    BalabanRGUniformLSIQuantitativeP81KernelPacket d N_c := by
  exact
    balaban_rg_uniform_lsi_quantitative_p81_kernel_packet_of_quantitative_p81_chosen_beta_packet d N_c
      (balaban_rg_uniform_lsi_quantitative_p81_chosen_beta_packet_of_quantitative_p81_obstruction_coherence
        d N_c coh)

/-- Canonical quantitative P81 kernel packet from the quantitative obstruction packet. -/
theorem balaban_rg_uniform_lsi_quantitative_p81_kernel_packet_of_quantitative_p81_obstruction_packet
    (d N_c : ℕ) [NeZero N_c] [∀ k, ActivityNorm d k]
    (packet : BalabanRGUniformLSIQuantitativeP81ObstructionPacket d N_c) :
    BalabanRGUniformLSIQuantitativeP81KernelPacket d N_c := by
  exact
    balaban_rg_uniform_lsi_quantitative_p81_kernel_packet_of_quantitative_p81_chosen_beta_packet d N_c
      (balaban_rg_uniform_lsi_quantitative_p81_chosen_beta_packet_of_quantitative_p81_obstruction_packet
        d N_c packet)

/-- Canonical quantitative P81 kernel packet from the quantitative P81 coherence hub together
with the theorem-side live target. -/
theorem balaban_rg_uniform_lsi_quantitative_p81_kernel_packet_of_quantitative_p81_coherence_and_live_target
    (d N_c : ℕ) [NeZero N_c] [∀ k, ActivityNorm d k]
    (coh : BalabanRGUniformLSIQuantitativeP81Coherence d N_c)
    (live : RGCauchyP81LiveTarget d N_c) :
    BalabanRGUniformLSIQuantitativeP81KernelPacket d N_c := by
  exact
    balaban_rg_uniform_lsi_quantitative_p81_kernel_packet_of_quantitative_frontier_and_live_target
      d N_c
      (quantitative_frontier_of_balaban_rg_uniform_lsi_quantitative_p81_coherence coh)
      live

/-- Canonical quantitative P81 kernel packet from the quantitative P81 packet. -/
theorem balaban_rg_uniform_lsi_quantitative_p81_kernel_packet_of_quantitative_p81_packet
    (d N_c : ℕ) [NeZero N_c] [∀ k, ActivityNorm d k]
    (packet : BalabanRGUniformLSIQuantitativeP81Packet d N_c) :
    BalabanRGUniformLSIQuantitativeP81KernelPacket d N_c := by
  exact
    balaban_rg_uniform_lsi_quantitative_p81_kernel_packet_of_quantitative_p81_chosen_beta_packet d N_c
      (balaban_rg_uniform_lsi_quantitative_p81_chosen_beta_packet_of_quantitative_p81_packet
        d N_c packet)

/-- Canonical quantitative P81 kernel packet from the quantitative load-bearing coherence hub
together with the theorem-side live target. -/
theorem balaban_rg_uniform_lsi_quantitative_p81_kernel_packet_of_quantitative_load_bearing_coherence_and_live_target
    (d N_c : ℕ) [NeZero N_c] [∀ k, ActivityNorm d k]
    (coh : BalabanRGUniformLSIQuantitativeLoadBearingCoherence d N_c)
    (live : RGCauchyP81LiveTarget d N_c) :
    BalabanRGUniformLSIQuantitativeP81KernelPacket d N_c := by
  exact
    balaban_rg_uniform_lsi_quantitative_p81_kernel_packet_of_quantitative_frontier_and_live_target
      d N_c
      (quantitative_frontier_of_balaban_rg_uniform_lsi_quantitative_load_bearing_coherence coh)
      live

/-- Canonical quantitative P81 kernel packet from the quantitative audit packet together with
the theorem-side live target. -/
theorem balaban_rg_uniform_lsi_quantitative_p81_kernel_packet_of_quantitative_audit_packet_and_live_target
    (d N_c : ℕ) [NeZero N_c] [∀ k, ActivityNorm d k]
    (packet : BalabanRGUniformLSIQuantitativeAuditPacket d N_c)
    (live : RGCauchyP81LiveTarget d N_c) :
    BalabanRGUniformLSIQuantitativeP81KernelPacket d N_c := by
  exact
    balaban_rg_uniform_lsi_quantitative_p81_kernel_packet_of_quantitative_frontier_and_live_target
      d N_c
      (quantitative_frontier_of_balaban_rg_uniform_lsi_quantitative_audit_packet packet)
      live

/-- Canonical quantitative P81 kernel packet from the quantitative audit coherence hub together
with the theorem-side live target. -/
theorem balaban_rg_uniform_lsi_quantitative_p81_kernel_packet_of_quantitative_audit_coherence_and_live_target
    (d N_c : ℕ) [NeZero N_c] [∀ k, ActivityNorm d k]
    (coh : BalabanRGUniformLSIQuantitativeAuditCoherence d N_c)
    (live : RGCauchyP81LiveTarget d N_c) :
    BalabanRGUniformLSIQuantitativeP81KernelPacket d N_c := by
  exact
    balaban_rg_uniform_lsi_quantitative_p81_kernel_packet_of_quantitative_frontier_and_live_target
      d N_c
      (quantitative_frontier_of_balaban_rg_uniform_lsi_quantitative_audit_coherence coh)
      live

/-- Projection to the chosen-beta theorem-side packet. -/
theorem quantitative_p81_chosen_beta_packet_of_balaban_rg_uniform_lsi_quantitative_p81_kernel_packet
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (packet : BalabanRGUniformLSIQuantitativeP81KernelPacket d N_c) :
    BalabanRGUniformLSIQuantitativeP81ChosenBetaPacket d N_c := by
  exact packet.quantitativeP81ChosenBetaPacket

/-- Projection to the witness-selected theorem-side packet. -/
theorem quantitative_p81_witness_packet_of_balaban_rg_uniform_lsi_quantitative_p81_kernel_packet
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (packet : BalabanRGUniformLSIQuantitativeP81KernelPacket d N_c) :
    BalabanRGUniformLSIQuantitativeP81WitnessPacket d N_c := by
  exact packet.quantitativeP81WitnessPacket

/-- Projection to the quantitative obstruction coherence hub. -/
theorem quantitative_p81_obstruction_coherence_of_balaban_rg_uniform_lsi_quantitative_p81_kernel_packet
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (packet : BalabanRGUniformLSIQuantitativeP81KernelPacket d N_c) :
    BalabanRGUniformLSIQuantitativeP81ObstructionCoherence d N_c := by
  exact packet.quantitativeP81ObstructionCoherence

/-- Projection to the quantitative obstruction packet. -/
theorem quantitative_p81_obstruction_packet_of_balaban_rg_uniform_lsi_quantitative_p81_kernel_packet
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (packet : BalabanRGUniformLSIQuantitativeP81KernelPacket d N_c) :
    BalabanRGUniformLSIQuantitativeP81ObstructionPacket d N_c := by
  exact packet.quantitativeP81ObstructionPacket

/-- Projection to the quantitative P81 coherence hub. -/
theorem quantitative_p81_coherence_of_balaban_rg_uniform_lsi_quantitative_p81_kernel_packet
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (packet : BalabanRGUniformLSIQuantitativeP81KernelPacket d N_c) :
    BalabanRGUniformLSIQuantitativeP81Coherence d N_c := by
  exact packet.quantitativeP81Coherence

/-- Projection to the quantitative P81 packet. -/
theorem quantitative_p81_packet_of_balaban_rg_uniform_lsi_quantitative_p81_kernel_packet
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (packet : BalabanRGUniformLSIQuantitativeP81KernelPacket d N_c) :
    BalabanRGUniformLSIQuantitativeP81Packet d N_c := by
  exact packet.quantitativeP81Packet

/-- Projection to the quantitative frontier. -/
theorem quantitative_frontier_of_balaban_rg_uniform_lsi_quantitative_p81_kernel_packet
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (packet : BalabanRGUniformLSIQuantitativeP81KernelPacket d N_c) :
    BalabanRGUniformLSIQuantitativeFrontier d N_c := by
  exact packet.quantitativeFrontier

/-- Projection to the theorem-side live target. -/
theorem theorem_live_target_of_balaban_rg_uniform_lsi_quantitative_p81_kernel_packet
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (packet : BalabanRGUniformLSIQuantitativeP81KernelPacket d N_c) :
    RGCauchyP81LiveTarget d N_c := by
  exact packet.theoremLiveTarget

/-- Projection to the short public P81 frontier. -/
theorem rg_cauchy_p81_frontier_of_balaban_rg_uniform_lsi_quantitative_p81_kernel_packet
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (packet : BalabanRGUniformLSIQuantitativeP81KernelPacket d N_c) :
    RGCauchyP81Frontier d N_c := by
  exact packet.p81Frontier

/-- Projection to the short theorem-side coherence packet. -/
theorem rg_cauchy_p81_coherence_packet_of_balaban_rg_uniform_lsi_quantitative_p81_kernel_packet
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (packet : BalabanRGUniformLSIQuantitativeP81KernelPacket d N_c) :
    RGCauchyP81CoherencePacket d N_c := by
  exact packet.p81CoherencePacket

/-- Projection to the explicit kernel output packet. -/
theorem rg_cauchy_p81_kernel_output_of_balaban_rg_uniform_lsi_quantitative_p81_kernel_packet
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (packet : BalabanRGUniformLSIQuantitativeP81KernelPacket d N_c) :
    RGCauchyP81KernelOutput d N_c := by
  exact packet.kernelOutput

/-- Projection to the explicit kernel input packet. -/
theorem rg_cauchy_p81_kernel_input_of_balaban_rg_uniform_lsi_quantitative_p81_kernel_packet
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (packet : BalabanRGUniformLSIQuantitativeP81KernelPacket d N_c) :
    RGCauchyP81KernelInput d N_c := by
  exact packet.kernelInput

/-- Projection to the P81 obligation surface. -/
theorem obligation_of_balaban_rg_uniform_lsi_quantitative_p81_kernel_packet
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (packet : BalabanRGUniformLSIQuantitativeP81KernelPacket d N_c) :
    RGCauchyP81Obligation d N_c := by
  exact packet.obligation

/-- Projection to the existential chosen-β witness. -/
theorem chosen_beta_witness_of_balaban_rg_uniform_lsi_quantitative_p81_kernel_packet
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (packet : BalabanRGUniformLSIQuantitativeP81KernelPacket d N_c) :
    ∃ β : ℝ, 1 ≤ β ∧ RGIncrementDecayBound d N_c β ∧ RGCauchySummabilityBound d N_c β := by
  exact packet.chosenBetaWitness

/-- Canonically chosen β carried by the theorem-side kernel packet. -/
def chosen_beta_of_balaban_rg_uniform_lsi_quantitative_p81_kernel_packet
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (packet : BalabanRGUniformLSIQuantitativeP81KernelPacket d N_c) : ℝ :=
  Classical.choose
    (chosen_beta_witness_of_balaban_rg_uniform_lsi_quantitative_p81_kernel_packet packet)

/-- The chosen β satisfies `1 ≤ β`. -/
theorem chosen_beta_ge_one_of_balaban_rg_uniform_lsi_quantitative_p81_kernel_packet
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (packet : BalabanRGUniformLSIQuantitativeP81KernelPacket d N_c) :
    1 ≤ chosen_beta_of_balaban_rg_uniform_lsi_quantitative_p81_kernel_packet packet := by
  simpa [chosen_beta_of_balaban_rg_uniform_lsi_quantitative_p81_kernel_packet] using
    (Classical.choose_spec
      (chosen_beta_witness_of_balaban_rg_uniform_lsi_quantitative_p81_kernel_packet packet)).1

/-- The chosen β satisfies increment decay. -/
theorem chosen_beta_increment_decay_bound_of_balaban_rg_uniform_lsi_quantitative_p81_kernel_packet
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (packet : BalabanRGUniformLSIQuantitativeP81KernelPacket d N_c) :
    RGIncrementDecayBound d N_c
      (chosen_beta_of_balaban_rg_uniform_lsi_quantitative_p81_kernel_packet packet) := by
  simpa [chosen_beta_of_balaban_rg_uniform_lsi_quantitative_p81_kernel_packet] using
    (Classical.choose_spec
      (chosen_beta_witness_of_balaban_rg_uniform_lsi_quantitative_p81_kernel_packet packet)).2.1

/-- The chosen β satisfies RG-Cauchy summability. -/
theorem chosen_beta_cauchy_summability_bound_of_balaban_rg_uniform_lsi_quantitative_p81_kernel_packet
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (packet : BalabanRGUniformLSIQuantitativeP81KernelPacket d N_c) :
    RGCauchySummabilityBound d N_c
      (chosen_beta_of_balaban_rg_uniform_lsi_quantitative_p81_kernel_packet packet) := by
  simpa [chosen_beta_of_balaban_rg_uniform_lsi_quantitative_p81_kernel_packet] using
    (Classical.choose_spec
      (chosen_beta_witness_of_balaban_rg_uniform_lsi_quantitative_p81_kernel_packet packet)).2.2

/-- Logical normal form: the theorem-side kernel packet is equivalent to the chosen-beta packet. -/
theorem balaban_rg_uniform_lsi_quantitative_p81_kernel_packet_iff_quantitative_p81_chosen_beta_packet
    (d N_c : ℕ) [NeZero N_c] [∀ k, ActivityNorm d k] :
    BalabanRGUniformLSIQuantitativeP81KernelPacket d N_c ↔
      BalabanRGUniformLSIQuantitativeP81ChosenBetaPacket d N_c := by
  constructor
  · intro packet
    exact packet.quantitativeP81ChosenBetaPacket
  · intro chosen
    exact
      balaban_rg_uniform_lsi_quantitative_p81_kernel_packet_of_quantitative_p81_chosen_beta_packet
        d N_c chosen

/-- Logical normal form: the theorem-side kernel packet is equivalent to the pair consisting
of the quantitative frontier and the theorem-side live target. -/
theorem balaban_rg_uniform_lsi_quantitative_p81_kernel_packet_iff_quantitative_frontier_and_live_target
    (d N_c : ℕ) [NeZero N_c] [∀ k, ActivityNorm d k] :
    BalabanRGUniformLSIQuantitativeP81KernelPacket d N_c ↔
      (BalabanRGUniformLSIQuantitativeFrontier d N_c ∧ RGCauchyP81LiveTarget d N_c) := by
  constructor
  · intro packet
    exact ⟨ packet.quantitativeFrontier, packet.theoremLiveTarget ⟩
  · intro h
    exact
      balaban_rg_uniform_lsi_quantitative_p81_kernel_packet_of_quantitative_frontier_and_live_target
        d N_c h.1 h.2

/-- Coherence: the kernel packet is propositionally equal to the canonical one reconstructed
from its quantitative frontier and theorem-side live target. -/
theorem balaban_rg_uniform_lsi_quantitative_p81_kernel_packet_eq_canonical_of_quantitative_frontier_and_live_target
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (packet : BalabanRGUniformLSIQuantitativeP81KernelPacket d N_c) :
    packet =
      balaban_rg_uniform_lsi_quantitative_p81_kernel_packet_of_quantitative_frontier_and_live_target d N_c
        (quantitative_frontier_of_balaban_rg_uniform_lsi_quantitative_p81_kernel_packet packet)
        (theorem_live_target_of_balaban_rg_uniform_lsi_quantitative_p81_kernel_packet packet) := by
  apply Subsingleton.elim

/-- Coherence: the kernel input is canonically reconstructed from the kernel output. -/
theorem rg_cauchy_p81_kernel_input_eq_canonical_of_quantitative_p81_kernel_packet
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (packet : BalabanRGUniformLSIQuantitativeP81KernelPacket d N_c) :
    rg_cauchy_p81_kernel_input_of_balaban_rg_uniform_lsi_quantitative_p81_kernel_packet packet =
      rg_cauchy_p81_kernel_input_of_output d N_c
        (rg_cauchy_p81_kernel_output_of_balaban_rg_uniform_lsi_quantitative_p81_kernel_packet packet) := by
  apply Subsingleton.elim

/-- Coherence: the obligation is canonically reconstructed from the kernel output. -/
theorem rg_cauchy_p81_obligation_eq_canonical_of_quantitative_p81_kernel_packet
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (packet : BalabanRGUniformLSIQuantitativeP81KernelPacket d N_c) :
    obligation_of_balaban_rg_uniform_lsi_quantitative_p81_kernel_packet packet =
      rg_cauchy_p81_obligation_of_output d N_c
        (rg_cauchy_p81_kernel_output_of_balaban_rg_uniform_lsi_quantitative_p81_kernel_packet packet) := by
  apply Subsingleton.elim

/-- Coherence: the theorem-side coherence packet is canonically reconstructed from the frontier. -/
theorem rg_cauchy_p81_coherence_packet_eq_canonical_of_quantitative_p81_kernel_packet
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (packet : BalabanRGUniformLSIQuantitativeP81KernelPacket d N_c) :
    rg_cauchy_p81_coherence_packet_of_balaban_rg_uniform_lsi_quantitative_p81_kernel_packet packet =
      rg_cauchy_p81_coherence_packet_of_frontier d N_c
        (rg_cauchy_p81_frontier_of_balaban_rg_uniform_lsi_quantitative_p81_kernel_packet packet) := by
  apply Subsingleton.elim

end

end YangMills.ClayCore
