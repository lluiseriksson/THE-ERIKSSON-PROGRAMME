import Mathlib
import YangMills.ClayCore.BalabanRG.BalabanRGUniformLSIQuantitativeP81ObstructionCoherence

namespace YangMills.ClayCore

open scoped BigOperators
open Classical
noncomputable section

/-- Witness-selected theorem-side packet for the current P81 bottleneck as seen from the direct
quantitative Balaban-RG / Haar-LSI route. It stays proposition-valued and stores only the
existential witnesses; the concrete exponents are selected canonically afterward via
`Classical.choose`. -/
structure BalabanRGUniformLSIQuantitativeP81WitnessPacket
    (d N_c : ℕ) [NeZero N_c] [∀ k, ActivityNorm d k] : Prop where
  quantitativeP81ObstructionCoherence : BalabanRGUniformLSIQuantitativeP81ObstructionCoherence d N_c
  quantitativeP81ObstructionPacket : BalabanRGUniformLSIQuantitativeP81ObstructionPacket d N_c
  quantitativeP81Coherence : BalabanRGUniformLSIQuantitativeP81Coherence d N_c
  quantitativeP81Packet : BalabanRGUniformLSIQuantitativeP81Packet d N_c
  quantitativeFrontier : BalabanRGUniformLSIQuantitativeFrontier d N_c
  theoremLiveTarget : RGCauchyP81LiveTarget d N_c
  p81Frontier : RGCauchyP81Frontier d N_c
  p81CoherencePacket : RGCauchyP81CoherencePacket d N_c
  incrementDecayWitness : ∃ β : ℝ, 1 ≤ β ∧ RGIncrementDecayBound d N_c β
  cauchySummabilityWitness : ∃ β : ℝ, 1 ≤ β ∧ RGCauchySummabilityBound d N_c β

/-- Canonical witness-selected theorem-side packet from the direct quantitative Haar-LSI frontier
together with the theorem-side live target. -/
theorem balaban_rg_uniform_lsi_quantitative_p81_witness_packet_of_quantitative_frontier_and_live_target
    (d N_c : ℕ) [NeZero N_c] [∀ k, ActivityNorm d k]
    (frontier : BalabanRGUniformLSIQuantitativeFrontier d N_c)
    (live : RGCauchyP81LiveTarget d N_c) :
    BalabanRGUniformLSIQuantitativeP81WitnessPacket d N_c := by
  let coh : BalabanRGUniformLSIQuantitativeP81ObstructionCoherence d N_c :=
    balaban_rg_uniform_lsi_quantitative_p81_obstruction_coherence_of_quantitative_frontier_and_live_target
      d N_c frontier live
  exact
    ⟨ coh,
      quantitative_p81_obstruction_packet_of_balaban_rg_uniform_lsi_quantitative_p81_obstruction_coherence coh,
      quantitative_p81_coherence_of_balaban_rg_uniform_lsi_quantitative_p81_obstruction_coherence coh,
      quantitative_p81_packet_of_balaban_rg_uniform_lsi_quantitative_p81_obstruction_coherence coh,
      quantitative_frontier_of_balaban_rg_uniform_lsi_quantitative_p81_obstruction_coherence coh,
      theorem_live_target_of_balaban_rg_uniform_lsi_quantitative_p81_obstruction_coherence coh,
      rg_cauchy_p81_frontier_of_balaban_rg_uniform_lsi_quantitative_p81_obstruction_coherence coh,
      rg_cauchy_p81_coherence_packet_of_balaban_rg_uniform_lsi_quantitative_p81_obstruction_coherence coh,
      rg_increment_decay_bound_of_balaban_rg_uniform_lsi_quantitative_p81_obstruction_coherence coh,
      rg_cauchy_summability_bound_of_balaban_rg_uniform_lsi_quantitative_p81_obstruction_coherence coh ⟩

/-- Canonical witness-selected theorem-side packet from the quantitative obstruction coherence hub. -/
theorem balaban_rg_uniform_lsi_quantitative_p81_witness_packet_of_quantitative_p81_obstruction_coherence
    (d N_c : ℕ) [NeZero N_c] [∀ k, ActivityNorm d k]
    (coh : BalabanRGUniformLSIQuantitativeP81ObstructionCoherence d N_c) :
    BalabanRGUniformLSIQuantitativeP81WitnessPacket d N_c := by
  exact
    ⟨ coh,
      quantitative_p81_obstruction_packet_of_balaban_rg_uniform_lsi_quantitative_p81_obstruction_coherence coh,
      quantitative_p81_coherence_of_balaban_rg_uniform_lsi_quantitative_p81_obstruction_coherence coh,
      quantitative_p81_packet_of_balaban_rg_uniform_lsi_quantitative_p81_obstruction_coherence coh,
      quantitative_frontier_of_balaban_rg_uniform_lsi_quantitative_p81_obstruction_coherence coh,
      theorem_live_target_of_balaban_rg_uniform_lsi_quantitative_p81_obstruction_coherence coh,
      rg_cauchy_p81_frontier_of_balaban_rg_uniform_lsi_quantitative_p81_obstruction_coherence coh,
      rg_cauchy_p81_coherence_packet_of_balaban_rg_uniform_lsi_quantitative_p81_obstruction_coherence coh,
      rg_increment_decay_bound_of_balaban_rg_uniform_lsi_quantitative_p81_obstruction_coherence coh,
      rg_cauchy_summability_bound_of_balaban_rg_uniform_lsi_quantitative_p81_obstruction_coherence coh ⟩

/-- Canonical witness-selected theorem-side packet from the quantitative obstruction packet. -/
theorem balaban_rg_uniform_lsi_quantitative_p81_witness_packet_of_quantitative_p81_obstruction_packet
    (d N_c : ℕ) [NeZero N_c] [∀ k, ActivityNorm d k]
    (packet : BalabanRGUniformLSIQuantitativeP81ObstructionPacket d N_c) :
    BalabanRGUniformLSIQuantitativeP81WitnessPacket d N_c := by
  exact
    balaban_rg_uniform_lsi_quantitative_p81_witness_packet_of_quantitative_p81_obstruction_coherence
      d N_c
      (balaban_rg_uniform_lsi_quantitative_p81_obstruction_coherence_of_quantitative_p81_obstruction_packet
        d N_c packet)

/-- Canonical witness-selected theorem-side packet from the quantitative P81 coherence hub
together with the theorem-side live target. -/
theorem balaban_rg_uniform_lsi_quantitative_p81_witness_packet_of_quantitative_p81_coherence_and_live_target
    (d N_c : ℕ) [NeZero N_c] [∀ k, ActivityNorm d k]
    (coh : BalabanRGUniformLSIQuantitativeP81Coherence d N_c)
    (live : RGCauchyP81LiveTarget d N_c) :
    BalabanRGUniformLSIQuantitativeP81WitnessPacket d N_c := by
  exact
    balaban_rg_uniform_lsi_quantitative_p81_witness_packet_of_quantitative_frontier_and_live_target
      d N_c
      (quantitative_frontier_of_balaban_rg_uniform_lsi_quantitative_p81_coherence coh)
      live

/-- Canonical witness-selected theorem-side packet from the quantitative P81 packet. -/
theorem balaban_rg_uniform_lsi_quantitative_p81_witness_packet_of_quantitative_p81_packet
    (d N_c : ℕ) [NeZero N_c] [∀ k, ActivityNorm d k]
    (packet : BalabanRGUniformLSIQuantitativeP81Packet d N_c) :
    BalabanRGUniformLSIQuantitativeP81WitnessPacket d N_c := by
  exact
    balaban_rg_uniform_lsi_quantitative_p81_witness_packet_of_quantitative_p81_obstruction_packet
      d N_c
      (balaban_rg_uniform_lsi_quantitative_p81_obstruction_packet_of_quantitative_p81_packet
        d N_c packet)

/-- Canonical witness-selected theorem-side packet from the quantitative load-bearing coherence
hub together with the theorem-side live target. -/
theorem balaban_rg_uniform_lsi_quantitative_p81_witness_packet_of_quantitative_load_bearing_coherence_and_live_target
    (d N_c : ℕ) [NeZero N_c] [∀ k, ActivityNorm d k]
    (coh : BalabanRGUniformLSIQuantitativeLoadBearingCoherence d N_c)
    (live : RGCauchyP81LiveTarget d N_c) :
    BalabanRGUniformLSIQuantitativeP81WitnessPacket d N_c := by
  exact
    balaban_rg_uniform_lsi_quantitative_p81_witness_packet_of_quantitative_frontier_and_live_target
      d N_c
      (quantitative_frontier_of_balaban_rg_uniform_lsi_quantitative_load_bearing_coherence coh)
      live

/-- Canonical witness-selected theorem-side packet from the quantitative audit packet together
with the theorem-side live target. -/
theorem balaban_rg_uniform_lsi_quantitative_p81_witness_packet_of_quantitative_audit_packet_and_live_target
    (d N_c : ℕ) [NeZero N_c] [∀ k, ActivityNorm d k]
    (packet : BalabanRGUniformLSIQuantitativeAuditPacket d N_c)
    (live : RGCauchyP81LiveTarget d N_c) :
    BalabanRGUniformLSIQuantitativeP81WitnessPacket d N_c := by
  exact
    balaban_rg_uniform_lsi_quantitative_p81_witness_packet_of_quantitative_frontier_and_live_target
      d N_c
      (quantitative_frontier_of_balaban_rg_uniform_lsi_quantitative_audit_packet packet)
      live

/-- Canonical witness-selected theorem-side packet from the quantitative audit coherence hub
together with the theorem-side live target. -/
theorem balaban_rg_uniform_lsi_quantitative_p81_witness_packet_of_quantitative_audit_coherence_and_live_target
    (d N_c : ℕ) [NeZero N_c] [∀ k, ActivityNorm d k]
    (coh : BalabanRGUniformLSIQuantitativeAuditCoherence d N_c)
    (live : RGCauchyP81LiveTarget d N_c) :
    BalabanRGUniformLSIQuantitativeP81WitnessPacket d N_c := by
  exact
    balaban_rg_uniform_lsi_quantitative_p81_witness_packet_of_quantitative_frontier_and_live_target
      d N_c
      (quantitative_frontier_of_balaban_rg_uniform_lsi_quantitative_audit_coherence coh)
      live

/-- Projection to the quantitative P81 obstruction coherence hub. -/
theorem quantitative_p81_obstruction_coherence_of_balaban_rg_uniform_lsi_quantitative_p81_witness_packet
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (packet : BalabanRGUniformLSIQuantitativeP81WitnessPacket d N_c) :
    BalabanRGUniformLSIQuantitativeP81ObstructionCoherence d N_c := by
  exact packet.quantitativeP81ObstructionCoherence

/-- Projection to the quantitative P81 obstruction packet. -/
theorem quantitative_p81_obstruction_packet_of_balaban_rg_uniform_lsi_quantitative_p81_witness_packet
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (packet : BalabanRGUniformLSIQuantitativeP81WitnessPacket d N_c) :
    BalabanRGUniformLSIQuantitativeP81ObstructionPacket d N_c := by
  exact packet.quantitativeP81ObstructionPacket

/-- Projection to the quantitative P81 coherence hub. -/
theorem quantitative_p81_coherence_of_balaban_rg_uniform_lsi_quantitative_p81_witness_packet
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (packet : BalabanRGUniformLSIQuantitativeP81WitnessPacket d N_c) :
    BalabanRGUniformLSIQuantitativeP81Coherence d N_c := by
  exact packet.quantitativeP81Coherence

/-- Projection to the quantitative P81 packet. -/
theorem quantitative_p81_packet_of_balaban_rg_uniform_lsi_quantitative_p81_witness_packet
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (packet : BalabanRGUniformLSIQuantitativeP81WitnessPacket d N_c) :
    BalabanRGUniformLSIQuantitativeP81Packet d N_c := by
  exact packet.quantitativeP81Packet

/-- Projection to the quantitative frontier. -/
theorem quantitative_frontier_of_balaban_rg_uniform_lsi_quantitative_p81_witness_packet
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (packet : BalabanRGUniformLSIQuantitativeP81WitnessPacket d N_c) :
    BalabanRGUniformLSIQuantitativeFrontier d N_c := by
  exact packet.quantitativeFrontier

/-- Projection to the theorem-side live target. -/
theorem theorem_live_target_of_balaban_rg_uniform_lsi_quantitative_p81_witness_packet
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (packet : BalabanRGUniformLSIQuantitativeP81WitnessPacket d N_c) :
    RGCauchyP81LiveTarget d N_c := by
  exact packet.theoremLiveTarget

/-- Projection to the short public P81 frontier. -/
theorem rg_cauchy_p81_frontier_of_balaban_rg_uniform_lsi_quantitative_p81_witness_packet
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (packet : BalabanRGUniformLSIQuantitativeP81WitnessPacket d N_c) :
    RGCauchyP81Frontier d N_c := by
  exact packet.p81Frontier

/-- Projection to the short theorem-side coherence packet. -/
theorem rg_cauchy_p81_coherence_packet_of_balaban_rg_uniform_lsi_quantitative_p81_witness_packet
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (packet : BalabanRGUniformLSIQuantitativeP81WitnessPacket d N_c) :
    RGCauchyP81CoherencePacket d N_c := by
  exact packet.p81CoherencePacket

/-- Projection to the existential increment-decay witness. -/
theorem rg_increment_decay_witness_of_balaban_rg_uniform_lsi_quantitative_p81_witness_packet
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (packet : BalabanRGUniformLSIQuantitativeP81WitnessPacket d N_c) :
    ∃ β : ℝ, 1 ≤ β ∧ RGIncrementDecayBound d N_c β := by
  exact packet.incrementDecayWitness

/-- Projection to the existential RG-Cauchy summability witness. -/
theorem rg_cauchy_summability_witness_of_balaban_rg_uniform_lsi_quantitative_p81_witness_packet
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (packet : BalabanRGUniformLSIQuantitativeP81WitnessPacket d N_c) :
    ∃ β : ℝ, 1 ≤ β ∧ RGCauchySummabilityBound d N_c β := by
  exact packet.cauchySummabilityWitness

/-- Canonically chosen increment-decay exponent extracted from the existential witness. -/
def increment_decay_beta_of_balaban_rg_uniform_lsi_quantitative_p81_witness_packet
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (packet : BalabanRGUniformLSIQuantitativeP81WitnessPacket d N_c) : ℝ :=
  Classical.choose
    (rg_increment_decay_witness_of_balaban_rg_uniform_lsi_quantitative_p81_witness_packet packet)

/-- The chosen increment-decay exponent satisfies the required lower bound. -/
theorem increment_decay_beta_ge_one_of_balaban_rg_uniform_lsi_quantitative_p81_witness_packet
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (packet : BalabanRGUniformLSIQuantitativeP81WitnessPacket d N_c) :
    1 ≤ increment_decay_beta_of_balaban_rg_uniform_lsi_quantitative_p81_witness_packet packet := by
  simpa [increment_decay_beta_of_balaban_rg_uniform_lsi_quantitative_p81_witness_packet] using
    (Classical.choose_spec
      (rg_increment_decay_witness_of_balaban_rg_uniform_lsi_quantitative_p81_witness_packet packet)).1

/-- The chosen increment-decay exponent satisfies the required bound. -/
theorem increment_decay_bound_of_balaban_rg_uniform_lsi_quantitative_p81_witness_packet
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (packet : BalabanRGUniformLSIQuantitativeP81WitnessPacket d N_c) :
    RGIncrementDecayBound d N_c
      (increment_decay_beta_of_balaban_rg_uniform_lsi_quantitative_p81_witness_packet packet) := by
  simpa [increment_decay_beta_of_balaban_rg_uniform_lsi_quantitative_p81_witness_packet] using
    (Classical.choose_spec
      (rg_increment_decay_witness_of_balaban_rg_uniform_lsi_quantitative_p81_witness_packet packet)).2

/-- Canonically chosen RG-Cauchy summability exponent extracted from the existential witness. -/
def cauchy_summability_beta_of_balaban_rg_uniform_lsi_quantitative_p81_witness_packet
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (packet : BalabanRGUniformLSIQuantitativeP81WitnessPacket d N_c) : ℝ :=
  Classical.choose
    (rg_cauchy_summability_witness_of_balaban_rg_uniform_lsi_quantitative_p81_witness_packet packet)

/-- The chosen RG-Cauchy summability exponent satisfies the required lower bound. -/
theorem cauchy_summability_beta_ge_one_of_balaban_rg_uniform_lsi_quantitative_p81_witness_packet
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (packet : BalabanRGUniformLSIQuantitativeP81WitnessPacket d N_c) :
    1 ≤ cauchy_summability_beta_of_balaban_rg_uniform_lsi_quantitative_p81_witness_packet packet := by
  simpa [cauchy_summability_beta_of_balaban_rg_uniform_lsi_quantitative_p81_witness_packet] using
    (Classical.choose_spec
      (rg_cauchy_summability_witness_of_balaban_rg_uniform_lsi_quantitative_p81_witness_packet packet)).1

/-- The chosen RG-Cauchy summability exponent satisfies the required bound. -/
theorem cauchy_summability_bound_of_balaban_rg_uniform_lsi_quantitative_p81_witness_packet
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (packet : BalabanRGUniformLSIQuantitativeP81WitnessPacket d N_c) :
    RGCauchySummabilityBound d N_c
      (cauchy_summability_beta_of_balaban_rg_uniform_lsi_quantitative_p81_witness_packet packet) := by
  simpa [cauchy_summability_beta_of_balaban_rg_uniform_lsi_quantitative_p81_witness_packet] using
    (Classical.choose_spec
      (rg_cauchy_summability_witness_of_balaban_rg_uniform_lsi_quantitative_p81_witness_packet packet)).2

/-- Logical normal form: the witness-selected theorem-side packet is equivalent to the
quantitative obstruction coherence hub. -/
theorem balaban_rg_uniform_lsi_quantitative_p81_witness_packet_iff_quantitative_p81_obstruction_coherence
    (d N_c : ℕ) [NeZero N_c] [∀ k, ActivityNorm d k] :
    BalabanRGUniformLSIQuantitativeP81WitnessPacket d N_c ↔
      BalabanRGUniformLSIQuantitativeP81ObstructionCoherence d N_c := by
  constructor
  · intro packet
    exact packet.quantitativeP81ObstructionCoherence
  · intro coh
    exact
      balaban_rg_uniform_lsi_quantitative_p81_witness_packet_of_quantitative_p81_obstruction_coherence
        d N_c coh

/-- Logical normal form: the witness-selected theorem-side packet is equivalent to the
quantitative obstruction packet. -/
theorem balaban_rg_uniform_lsi_quantitative_p81_witness_packet_iff_quantitative_p81_obstruction_packet
    (d N_c : ℕ) [NeZero N_c] [∀ k, ActivityNorm d k] :
    BalabanRGUniformLSIQuantitativeP81WitnessPacket d N_c ↔
      BalabanRGUniformLSIQuantitativeP81ObstructionPacket d N_c := by
  constructor
  · intro packet
    exact packet.quantitativeP81ObstructionPacket
  · intro obstruction
    exact
      balaban_rg_uniform_lsi_quantitative_p81_witness_packet_of_quantitative_p81_obstruction_packet
        d N_c obstruction

/-- Logical normal form: the witness-selected theorem-side packet is equivalent to the pair
consisting of the direct quantitative frontier and the theorem-side live target. -/
theorem balaban_rg_uniform_lsi_quantitative_p81_witness_packet_iff_quantitative_frontier_and_live_target
    (d N_c : ℕ) [NeZero N_c] [∀ k, ActivityNorm d k] :
    BalabanRGUniformLSIQuantitativeP81WitnessPacket d N_c ↔
      (BalabanRGUniformLSIQuantitativeFrontier d N_c ∧ RGCauchyP81LiveTarget d N_c) := by
  constructor
  · intro packet
    exact ⟨ packet.quantitativeFrontier, packet.theoremLiveTarget ⟩
  · intro h
    exact
      balaban_rg_uniform_lsi_quantitative_p81_witness_packet_of_quantitative_frontier_and_live_target
        d N_c h.1 h.2

/-- Logical normal form: the witness-selected theorem-side packet is equivalent to the
quantitative P81 packet. -/
theorem balaban_rg_uniform_lsi_quantitative_p81_witness_packet_iff_quantitative_p81_packet
    (d N_c : ℕ) [NeZero N_c] [∀ k, ActivityNorm d k] :
    BalabanRGUniformLSIQuantitativeP81WitnessPacket d N_c ↔
      BalabanRGUniformLSIQuantitativeP81Packet d N_c := by
  constructor
  · intro packet
    exact packet.quantitativeP81Packet
  · intro p81packet
    exact
      balaban_rg_uniform_lsi_quantitative_p81_witness_packet_of_quantitative_p81_packet
        d N_c p81packet

/-- Coherence: the witness-selected packet is propositionally equal to the canonical one
reconstructed from its quantitative frontier and theorem-side live target. -/
theorem balaban_rg_uniform_lsi_quantitative_p81_witness_packet_eq_canonical_of_quantitative_frontier_and_live_target
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (packet : BalabanRGUniformLSIQuantitativeP81WitnessPacket d N_c) :
    packet =
      balaban_rg_uniform_lsi_quantitative_p81_witness_packet_of_quantitative_frontier_and_live_target d N_c
        (quantitative_frontier_of_balaban_rg_uniform_lsi_quantitative_p81_witness_packet packet)
        (theorem_live_target_of_balaban_rg_uniform_lsi_quantitative_p81_witness_packet packet) := by
  apply Subsingleton.elim

/-- Coherence: the existential increment-decay witness agrees canonically with the one already
carried by the quantitative obstruction coherence surface. -/
theorem rg_increment_decay_witness_eq_canonical_of_quantitative_p81_witness_packet
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (packet : BalabanRGUniformLSIQuantitativeP81WitnessPacket d N_c) :
    rg_increment_decay_witness_of_balaban_rg_uniform_lsi_quantitative_p81_witness_packet packet =
      rg_increment_decay_bound_of_balaban_rg_uniform_lsi_quantitative_p81_obstruction_coherence
        (quantitative_p81_obstruction_coherence_of_balaban_rg_uniform_lsi_quantitative_p81_witness_packet packet) := by
  apply Subsingleton.elim

/-- Coherence: the existential RG-Cauchy summability witness agrees canonically with the one
already carried by the quantitative obstruction coherence surface. -/
theorem rg_cauchy_summability_witness_eq_canonical_of_quantitative_p81_witness_packet
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (packet : BalabanRGUniformLSIQuantitativeP81WitnessPacket d N_c) :
    rg_cauchy_summability_witness_of_balaban_rg_uniform_lsi_quantitative_p81_witness_packet packet =
      rg_cauchy_summability_bound_of_balaban_rg_uniform_lsi_quantitative_p81_obstruction_coherence
        (quantitative_p81_obstruction_coherence_of_balaban_rg_uniform_lsi_quantitative_p81_witness_packet packet) := by
  apply Subsingleton.elim

end

end YangMills.ClayCore
