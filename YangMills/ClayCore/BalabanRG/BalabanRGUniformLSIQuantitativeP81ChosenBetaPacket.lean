import Mathlib
import YangMills.ClayCore.BalabanRG.BalabanRGUniformLSIQuantitativeP81WitnessPacket

namespace YangMills.ClayCore

open scoped BigOperators
open Classical
noncomputable section

/-- Canonical theorem-side packet selecting one β from the quantitative P81 witness surface.
The selected β is the canonical increment-decay exponent already extracted by the witness packet;
RG-Cauchy summability is then recovered for the same β via the standard implication
`increment_decay_implies_cauchy_summability`. -/
structure BalabanRGUniformLSIQuantitativeP81ChosenBetaPacket
    (d N_c : ℕ) [NeZero N_c] [∀ k, ActivityNorm d k] : Prop where
  quantitativeP81WitnessPacket : BalabanRGUniformLSIQuantitativeP81WitnessPacket d N_c
  quantitativeP81ObstructionCoherence : BalabanRGUniformLSIQuantitativeP81ObstructionCoherence d N_c
  quantitativeP81ObstructionPacket : BalabanRGUniformLSIQuantitativeP81ObstructionPacket d N_c
  quantitativeP81Coherence : BalabanRGUniformLSIQuantitativeP81Coherence d N_c
  quantitativeP81Packet : BalabanRGUniformLSIQuantitativeP81Packet d N_c
  quantitativeFrontier : BalabanRGUniformLSIQuantitativeFrontier d N_c
  theoremLiveTarget : RGCauchyP81LiveTarget d N_c
  p81Frontier : RGCauchyP81Frontier d N_c
  p81CoherencePacket : RGCauchyP81CoherencePacket d N_c
  chosenBetaWitness : ∃ β : ℝ, 1 ≤ β ∧ RGIncrementDecayBound d N_c β ∧ RGCauchySummabilityBound d N_c β

/-- Canonical chosen-beta theorem-side packet from the direct quantitative frontier together with
the theorem-side live target. -/
theorem balaban_rg_uniform_lsi_quantitative_p81_chosen_beta_packet_of_quantitative_frontier_and_live_target
    (d N_c : ℕ) [NeZero N_c] [∀ k, ActivityNorm d k]
    (frontier : BalabanRGUniformLSIQuantitativeFrontier d N_c)
    (live : RGCauchyP81LiveTarget d N_c) :
    BalabanRGUniformLSIQuantitativeP81ChosenBetaPacket d N_c := by
  let packet : BalabanRGUniformLSIQuantitativeP81WitnessPacket d N_c :=
    balaban_rg_uniform_lsi_quantitative_p81_witness_packet_of_quantitative_frontier_and_live_target
      d N_c frontier live
  let β : ℝ :=
    increment_decay_beta_of_balaban_rg_uniform_lsi_quantitative_p81_witness_packet packet
  have hβ1 : 1 ≤ β := by
    exact increment_decay_beta_ge_one_of_balaban_rg_uniform_lsi_quantitative_p81_witness_packet packet
  have hdec : RGIncrementDecayBound d N_c β := by
    exact increment_decay_bound_of_balaban_rg_uniform_lsi_quantitative_p81_witness_packet packet
  have hsum : RGCauchySummabilityBound d N_c β := by
    exact increment_decay_implies_cauchy_summability d N_c β hdec
  exact
    ⟨ packet,
      quantitative_p81_obstruction_coherence_of_balaban_rg_uniform_lsi_quantitative_p81_witness_packet packet,
      quantitative_p81_obstruction_packet_of_balaban_rg_uniform_lsi_quantitative_p81_witness_packet packet,
      quantitative_p81_coherence_of_balaban_rg_uniform_lsi_quantitative_p81_witness_packet packet,
      quantitative_p81_packet_of_balaban_rg_uniform_lsi_quantitative_p81_witness_packet packet,
      quantitative_frontier_of_balaban_rg_uniform_lsi_quantitative_p81_witness_packet packet,
      theorem_live_target_of_balaban_rg_uniform_lsi_quantitative_p81_witness_packet packet,
      rg_cauchy_p81_frontier_of_balaban_rg_uniform_lsi_quantitative_p81_witness_packet packet,
      rg_cauchy_p81_coherence_packet_of_balaban_rg_uniform_lsi_quantitative_p81_witness_packet packet,
      ⟨ β, hβ1, hdec, hsum ⟩ ⟩

/-- Canonical chosen-beta theorem-side packet from the witness-selected theorem-side packet. -/
theorem balaban_rg_uniform_lsi_quantitative_p81_chosen_beta_packet_of_quantitative_p81_witness_packet
    (d N_c : ℕ) [NeZero N_c] [∀ k, ActivityNorm d k]
    (packet : BalabanRGUniformLSIQuantitativeP81WitnessPacket d N_c) :
    BalabanRGUniformLSIQuantitativeP81ChosenBetaPacket d N_c := by
  let β : ℝ :=
    increment_decay_beta_of_balaban_rg_uniform_lsi_quantitative_p81_witness_packet packet
  have hβ1 : 1 ≤ β := by
    exact increment_decay_beta_ge_one_of_balaban_rg_uniform_lsi_quantitative_p81_witness_packet packet
  have hdec : RGIncrementDecayBound d N_c β := by
    exact increment_decay_bound_of_balaban_rg_uniform_lsi_quantitative_p81_witness_packet packet
  have hsum : RGCauchySummabilityBound d N_c β := by
    exact increment_decay_implies_cauchy_summability d N_c β hdec
  exact
    ⟨ packet,
      quantitative_p81_obstruction_coherence_of_balaban_rg_uniform_lsi_quantitative_p81_witness_packet packet,
      quantitative_p81_obstruction_packet_of_balaban_rg_uniform_lsi_quantitative_p81_witness_packet packet,
      quantitative_p81_coherence_of_balaban_rg_uniform_lsi_quantitative_p81_witness_packet packet,
      quantitative_p81_packet_of_balaban_rg_uniform_lsi_quantitative_p81_witness_packet packet,
      quantitative_frontier_of_balaban_rg_uniform_lsi_quantitative_p81_witness_packet packet,
      theorem_live_target_of_balaban_rg_uniform_lsi_quantitative_p81_witness_packet packet,
      rg_cauchy_p81_frontier_of_balaban_rg_uniform_lsi_quantitative_p81_witness_packet packet,
      rg_cauchy_p81_coherence_packet_of_balaban_rg_uniform_lsi_quantitative_p81_witness_packet packet,
      ⟨ β, hβ1, hdec, hsum ⟩ ⟩

/-- Canonical chosen-beta theorem-side packet from the quantitative obstruction coherence hub. -/
theorem balaban_rg_uniform_lsi_quantitative_p81_chosen_beta_packet_of_quantitative_p81_obstruction_coherence
    (d N_c : ℕ) [NeZero N_c] [∀ k, ActivityNorm d k]
    (coh : BalabanRGUniformLSIQuantitativeP81ObstructionCoherence d N_c) :
    BalabanRGUniformLSIQuantitativeP81ChosenBetaPacket d N_c := by
  exact
    balaban_rg_uniform_lsi_quantitative_p81_chosen_beta_packet_of_quantitative_p81_witness_packet
      d N_c
      (balaban_rg_uniform_lsi_quantitative_p81_witness_packet_of_quantitative_p81_obstruction_coherence
        d N_c coh)

/-- Canonical chosen-beta theorem-side packet from the quantitative obstruction packet. -/
theorem balaban_rg_uniform_lsi_quantitative_p81_chosen_beta_packet_of_quantitative_p81_obstruction_packet
    (d N_c : ℕ) [NeZero N_c] [∀ k, ActivityNorm d k]
    (packet : BalabanRGUniformLSIQuantitativeP81ObstructionPacket d N_c) :
    BalabanRGUniformLSIQuantitativeP81ChosenBetaPacket d N_c := by
  exact
    balaban_rg_uniform_lsi_quantitative_p81_chosen_beta_packet_of_quantitative_p81_witness_packet
      d N_c
      (balaban_rg_uniform_lsi_quantitative_p81_witness_packet_of_quantitative_p81_obstruction_packet
        d N_c packet)

/-- Canonical chosen-beta theorem-side packet from the quantitative P81 coherence hub together
with the theorem-side live target. -/
theorem balaban_rg_uniform_lsi_quantitative_p81_chosen_beta_packet_of_quantitative_p81_coherence_and_live_target
    (d N_c : ℕ) [NeZero N_c] [∀ k, ActivityNorm d k]
    (coh : BalabanRGUniformLSIQuantitativeP81Coherence d N_c)
    (live : RGCauchyP81LiveTarget d N_c) :
    BalabanRGUniformLSIQuantitativeP81ChosenBetaPacket d N_c := by
  exact
    balaban_rg_uniform_lsi_quantitative_p81_chosen_beta_packet_of_quantitative_frontier_and_live_target
      d N_c
      (quantitative_frontier_of_balaban_rg_uniform_lsi_quantitative_p81_coherence coh)
      live

/-- Canonical chosen-beta theorem-side packet from the quantitative P81 packet. -/
theorem balaban_rg_uniform_lsi_quantitative_p81_chosen_beta_packet_of_quantitative_p81_packet
    (d N_c : ℕ) [NeZero N_c] [∀ k, ActivityNorm d k]
    (packet : BalabanRGUniformLSIQuantitativeP81Packet d N_c) :
    BalabanRGUniformLSIQuantitativeP81ChosenBetaPacket d N_c := by
  exact
    balaban_rg_uniform_lsi_quantitative_p81_chosen_beta_packet_of_quantitative_p81_witness_packet
      d N_c
      (balaban_rg_uniform_lsi_quantitative_p81_witness_packet_of_quantitative_p81_packet
        d N_c packet)

/-- Canonical chosen-beta theorem-side packet from the quantitative load-bearing coherence hub
together with the theorem-side live target. -/
theorem balaban_rg_uniform_lsi_quantitative_p81_chosen_beta_packet_of_quantitative_load_bearing_coherence_and_live_target
    (d N_c : ℕ) [NeZero N_c] [∀ k, ActivityNorm d k]
    (coh : BalabanRGUniformLSIQuantitativeLoadBearingCoherence d N_c)
    (live : RGCauchyP81LiveTarget d N_c) :
    BalabanRGUniformLSIQuantitativeP81ChosenBetaPacket d N_c := by
  exact
    balaban_rg_uniform_lsi_quantitative_p81_chosen_beta_packet_of_quantitative_frontier_and_live_target
      d N_c
      (quantitative_frontier_of_balaban_rg_uniform_lsi_quantitative_load_bearing_coherence coh)
      live

/-- Canonical chosen-beta theorem-side packet from the quantitative audit packet together with
the theorem-side live target. -/
theorem balaban_rg_uniform_lsi_quantitative_p81_chosen_beta_packet_of_quantitative_audit_packet_and_live_target
    (d N_c : ℕ) [NeZero N_c] [∀ k, ActivityNorm d k]
    (packet : BalabanRGUniformLSIQuantitativeAuditPacket d N_c)
    (live : RGCauchyP81LiveTarget d N_c) :
    BalabanRGUniformLSIQuantitativeP81ChosenBetaPacket d N_c := by
  exact
    balaban_rg_uniform_lsi_quantitative_p81_chosen_beta_packet_of_quantitative_frontier_and_live_target
      d N_c
      (quantitative_frontier_of_balaban_rg_uniform_lsi_quantitative_audit_packet packet)
      live

/-- Canonical chosen-beta theorem-side packet from the quantitative audit coherence hub together
with the theorem-side live target. -/
theorem balaban_rg_uniform_lsi_quantitative_p81_chosen_beta_packet_of_quantitative_audit_coherence_and_live_target
    (d N_c : ℕ) [NeZero N_c] [∀ k, ActivityNorm d k]
    (coh : BalabanRGUniformLSIQuantitativeAuditCoherence d N_c)
    (live : RGCauchyP81LiveTarget d N_c) :
    BalabanRGUniformLSIQuantitativeP81ChosenBetaPacket d N_c := by
  exact
    balaban_rg_uniform_lsi_quantitative_p81_chosen_beta_packet_of_quantitative_frontier_and_live_target
      d N_c
      (quantitative_frontier_of_balaban_rg_uniform_lsi_quantitative_audit_coherence coh)
      live

/-- Projection to the witness-selected theorem-side packet. -/
theorem quantitative_p81_witness_packet_of_balaban_rg_uniform_lsi_quantitative_p81_chosen_beta_packet
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (packet : BalabanRGUniformLSIQuantitativeP81ChosenBetaPacket d N_c) :
    BalabanRGUniformLSIQuantitativeP81WitnessPacket d N_c := by
  exact packet.quantitativeP81WitnessPacket

/-- Projection to the quantitative obstruction coherence hub. -/
theorem quantitative_p81_obstruction_coherence_of_balaban_rg_uniform_lsi_quantitative_p81_chosen_beta_packet
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (packet : BalabanRGUniformLSIQuantitativeP81ChosenBetaPacket d N_c) :
    BalabanRGUniformLSIQuantitativeP81ObstructionCoherence d N_c := by
  exact packet.quantitativeP81ObstructionCoherence

/-- Projection to the quantitative obstruction packet. -/
theorem quantitative_p81_obstruction_packet_of_balaban_rg_uniform_lsi_quantitative_p81_chosen_beta_packet
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (packet : BalabanRGUniformLSIQuantitativeP81ChosenBetaPacket d N_c) :
    BalabanRGUniformLSIQuantitativeP81ObstructionPacket d N_c := by
  exact packet.quantitativeP81ObstructionPacket

/-- Projection to the quantitative P81 coherence hub. -/
theorem quantitative_p81_coherence_of_balaban_rg_uniform_lsi_quantitative_p81_chosen_beta_packet
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (packet : BalabanRGUniformLSIQuantitativeP81ChosenBetaPacket d N_c) :
    BalabanRGUniformLSIQuantitativeP81Coherence d N_c := by
  exact packet.quantitativeP81Coherence

/-- Projection to the quantitative P81 packet. -/
theorem quantitative_p81_packet_of_balaban_rg_uniform_lsi_quantitative_p81_chosen_beta_packet
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (packet : BalabanRGUniformLSIQuantitativeP81ChosenBetaPacket d N_c) :
    BalabanRGUniformLSIQuantitativeP81Packet d N_c := by
  exact packet.quantitativeP81Packet

/-- Projection to the quantitative frontier. -/
theorem quantitative_frontier_of_balaban_rg_uniform_lsi_quantitative_p81_chosen_beta_packet
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (packet : BalabanRGUniformLSIQuantitativeP81ChosenBetaPacket d N_c) :
    BalabanRGUniformLSIQuantitativeFrontier d N_c := by
  exact packet.quantitativeFrontier

/-- Projection to the theorem-side live target. -/
theorem theorem_live_target_of_balaban_rg_uniform_lsi_quantitative_p81_chosen_beta_packet
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (packet : BalabanRGUniformLSIQuantitativeP81ChosenBetaPacket d N_c) :
    RGCauchyP81LiveTarget d N_c := by
  exact packet.theoremLiveTarget

/-- Projection to the short public P81 frontier. -/
theorem rg_cauchy_p81_frontier_of_balaban_rg_uniform_lsi_quantitative_p81_chosen_beta_packet
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (packet : BalabanRGUniformLSIQuantitativeP81ChosenBetaPacket d N_c) :
    RGCauchyP81Frontier d N_c := by
  exact packet.p81Frontier

/-- Projection to the short theorem-side coherence packet. -/
theorem rg_cauchy_p81_coherence_packet_of_balaban_rg_uniform_lsi_quantitative_p81_chosen_beta_packet
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (packet : BalabanRGUniformLSIQuantitativeP81ChosenBetaPacket d N_c) :
    RGCauchyP81CoherencePacket d N_c := by
  exact packet.p81CoherencePacket

/-- Projection to the existential chosen-beta witness. -/
theorem chosen_beta_witness_of_balaban_rg_uniform_lsi_quantitative_p81_chosen_beta_packet
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (packet : BalabanRGUniformLSIQuantitativeP81ChosenBetaPacket d N_c) :
    ∃ β : ℝ, 1 ≤ β ∧ RGIncrementDecayBound d N_c β ∧ RGCauchySummabilityBound d N_c β := by
  exact packet.chosenBetaWitness

/-- Canonically chosen β carrying both increment decay and summability. -/
def chosen_beta_of_balaban_rg_uniform_lsi_quantitative_p81_chosen_beta_packet
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (packet : BalabanRGUniformLSIQuantitativeP81ChosenBetaPacket d N_c) : ℝ :=
  Classical.choose
    (chosen_beta_witness_of_balaban_rg_uniform_lsi_quantitative_p81_chosen_beta_packet packet)

/-- The chosen β satisfies the lower bound `1 ≤ β`. -/
theorem chosen_beta_ge_one_of_balaban_rg_uniform_lsi_quantitative_p81_chosen_beta_packet
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (packet : BalabanRGUniformLSIQuantitativeP81ChosenBetaPacket d N_c) :
    1 ≤ chosen_beta_of_balaban_rg_uniform_lsi_quantitative_p81_chosen_beta_packet packet := by
  simpa [chosen_beta_of_balaban_rg_uniform_lsi_quantitative_p81_chosen_beta_packet] using
    (Classical.choose_spec
      (chosen_beta_witness_of_balaban_rg_uniform_lsi_quantitative_p81_chosen_beta_packet packet)).1

/-- The chosen β satisfies the increment-decay bound. -/
theorem chosen_beta_increment_decay_bound_of_balaban_rg_uniform_lsi_quantitative_p81_chosen_beta_packet
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (packet : BalabanRGUniformLSIQuantitativeP81ChosenBetaPacket d N_c) :
    RGIncrementDecayBound d N_c
      (chosen_beta_of_balaban_rg_uniform_lsi_quantitative_p81_chosen_beta_packet packet) := by
  simpa [chosen_beta_of_balaban_rg_uniform_lsi_quantitative_p81_chosen_beta_packet] using
    (Classical.choose_spec
      (chosen_beta_witness_of_balaban_rg_uniform_lsi_quantitative_p81_chosen_beta_packet packet)).2.1

/-- The chosen β satisfies the RG-Cauchy summability bound. -/
theorem chosen_beta_cauchy_summability_bound_of_balaban_rg_uniform_lsi_quantitative_p81_chosen_beta_packet
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (packet : BalabanRGUniformLSIQuantitativeP81ChosenBetaPacket d N_c) :
    RGCauchySummabilityBound d N_c
      (chosen_beta_of_balaban_rg_uniform_lsi_quantitative_p81_chosen_beta_packet packet) := by
  simpa [chosen_beta_of_balaban_rg_uniform_lsi_quantitative_p81_chosen_beta_packet] using
    (Classical.choose_spec
      (chosen_beta_witness_of_balaban_rg_uniform_lsi_quantitative_p81_chosen_beta_packet packet)).2.2

/-- Logical normal form: the chosen-beta theorem-side packet is equivalent to the witness-selected
theorem-side packet. -/
theorem balaban_rg_uniform_lsi_quantitative_p81_chosen_beta_packet_iff_quantitative_p81_witness_packet
    (d N_c : ℕ) [NeZero N_c] [∀ k, ActivityNorm d k] :
    BalabanRGUniformLSIQuantitativeP81ChosenBetaPacket d N_c ↔
      BalabanRGUniformLSIQuantitativeP81WitnessPacket d N_c := by
  constructor
  · intro packet
    exact packet.quantitativeP81WitnessPacket
  · intro witness
    exact
      balaban_rg_uniform_lsi_quantitative_p81_chosen_beta_packet_of_quantitative_p81_witness_packet
        d N_c witness

/-- Logical normal form: the chosen-beta theorem-side packet is equivalent to the pair
consisting of the direct quantitative frontier and the theorem-side live target. -/
theorem balaban_rg_uniform_lsi_quantitative_p81_chosen_beta_packet_iff_quantitative_frontier_and_live_target
    (d N_c : ℕ) [NeZero N_c] [∀ k, ActivityNorm d k] :
    BalabanRGUniformLSIQuantitativeP81ChosenBetaPacket d N_c ↔
      (BalabanRGUniformLSIQuantitativeFrontier d N_c ∧ RGCauchyP81LiveTarget d N_c) := by
  constructor
  · intro packet
    exact ⟨ packet.quantitativeFrontier, packet.theoremLiveTarget ⟩
  · intro h
    exact
      balaban_rg_uniform_lsi_quantitative_p81_chosen_beta_packet_of_quantitative_frontier_and_live_target
        d N_c h.1 h.2

/-- Coherence: the chosen-beta packet is propositionally equal to the canonical one reconstructed
from its quantitative frontier and theorem-side live target. -/
theorem balaban_rg_uniform_lsi_quantitative_p81_chosen_beta_packet_eq_canonical_of_quantitative_frontier_and_live_target
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (packet : BalabanRGUniformLSIQuantitativeP81ChosenBetaPacket d N_c) :
    packet =
      balaban_rg_uniform_lsi_quantitative_p81_chosen_beta_packet_of_quantitative_frontier_and_live_target d N_c
        (quantitative_frontier_of_balaban_rg_uniform_lsi_quantitative_p81_chosen_beta_packet packet)
        (theorem_live_target_of_balaban_rg_uniform_lsi_quantitative_p81_chosen_beta_packet packet) := by
  apply Subsingleton.elim

/-- Coherence: the existential chosen-beta witness agrees canonically with the one reconstructed
from the witness-selected theorem-side packet. -/
theorem chosen_beta_witness_eq_canonical_of_quantitative_p81_chosen_beta_packet
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (packet : BalabanRGUniformLSIQuantitativeP81ChosenBetaPacket d N_c) :
    chosen_beta_witness_of_balaban_rg_uniform_lsi_quantitative_p81_chosen_beta_packet packet =
      chosen_beta_witness_of_balaban_rg_uniform_lsi_quantitative_p81_chosen_beta_packet
        (balaban_rg_uniform_lsi_quantitative_p81_chosen_beta_packet_of_quantitative_p81_witness_packet d N_c
          (quantitative_p81_witness_packet_of_balaban_rg_uniform_lsi_quantitative_p81_chosen_beta_packet packet)) := by
  apply Subsingleton.elim

end

end YangMills.ClayCore
