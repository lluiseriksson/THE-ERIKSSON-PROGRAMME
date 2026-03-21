import Mathlib
import YangMills.ClayCore.BalabanRG.BalabanRGUniformLSIObstructionPacket

namespace YangMills.ClayCore

/-- Unified public packet for the current load-bearing Pillar II surface of the
Balaban-RG / Haar-LSI lane: it carries both the still-live obstruction side and
the currently exported closure side. -/
structure BalabanRGUniformLSIPillarIIPacket (d N_c : ℕ) [NeZero N_c] : Prop where
  activation : BalabanRGUniformLSIActivationData d N_c
  frontier : BalabanRGUniformLSIFrontier d N_c
  directInput : BalabanRGUniformLSIDirectInput d N_c
  concreteInput : BalabanRGUniformLSIConcreteInput d N_c
  obstruction : BalabanRGUniformLSIObstructionPacket d N_c
  endToEnd : BalabanRGUniformLSIEndToEndPacket d N_c
  facade : BalabanRGUniformLSIPublicFacade d N_c
  closure : BalabanRGUniformLSIClosurePackage d N_c
  registry : BalabanRGUniformLSIEquivalenceRegistry d N_c
  lastMile : BalabanRGUniformLSILastMileOutput d N_c

/-- Canonical Pillar II packet from the abstract activation packet. -/
theorem balaban_rg_uniform_lsi_pillar_ii_packet_of_activation_data
    (d N_c : ℕ) [NeZero N_c]
    (data : BalabanRGUniformLSIActivationData d N_c) :
    BalabanRGUniformLSIPillarIIPacket d N_c := by
  let frontier : BalabanRGUniformLSIFrontier d N_c :=
    balaban_rg_uniform_lsi_frontier_of_activation_data d N_c data
  let directInput : BalabanRGUniformLSIDirectInput d N_c :=
    balaban_rg_uniform_lsi_direct_input_of_activation_data data
  let concreteInput : BalabanRGUniformLSIConcreteInput d N_c :=
    balaban_rg_uniform_lsi_concrete_input_of_activation_data data
  let obstruction : BalabanRGUniformLSIObstructionPacket d N_c :=
    balaban_rg_uniform_lsi_obstruction_packet_of_activation_data d N_c data
  let endToEnd : BalabanRGUniformLSIEndToEndPacket d N_c :=
    balaban_rg_uniform_lsi_end_to_end_packet_of_activation_data d N_c data
  let facade : BalabanRGUniformLSIPublicFacade d N_c :=
    balaban_rg_uniform_lsi_public_facade_of_activation_data d N_c data
  let closure : BalabanRGUniformLSIClosurePackage d N_c :=
    balaban_rg_uniform_lsi_closure_package_of_activation_data d N_c data
  let registry : BalabanRGUniformLSIEquivalenceRegistry d N_c :=
    balaban_rg_uniform_lsi_equivalence_registry_of_activation_data d N_c data
  let lastMile : BalabanRGUniformLSILastMileOutput d N_c :=
    balaban_rg_uniform_lsi_last_mile_output_of_activation_data d N_c data
  exact
    { activation := data
      frontier := frontier
      directInput := directInput
      concreteInput := concreteInput
      obstruction := obstruction
      endToEnd := endToEnd
      facade := facade
      closure := closure
      registry := registry
      lastMile := lastMile }

/-- Canonical Pillar II packet from the short public frontier. -/
theorem balaban_rg_uniform_lsi_pillar_ii_packet_of_frontier
    {d N_c : ℕ} [NeZero N_c]
    (frontier : BalabanRGUniformLSIFrontier d N_c) :
    BalabanRGUniformLSIPillarIIPacket d N_c := by
  exact
    balaban_rg_uniform_lsi_pillar_ii_packet_of_activation_data d N_c
      (activation_data_of_balaban_rg_uniform_lsi_frontier frontier)

/-- Canonical Pillar II packet from the direct input packet. -/
theorem balaban_rg_uniform_lsi_pillar_ii_packet_of_direct_input
    (d N_c : ℕ) [NeZero N_c]
    (input : BalabanRGUniformLSIDirectInput d N_c) :
    BalabanRGUniformLSIPillarIIPacket d N_c := by
  exact
    balaban_rg_uniform_lsi_pillar_ii_packet_of_activation_data d N_c
      (activation_data_of_balaban_rg_uniform_lsi_direct_input d N_c input)

/-- Canonical Pillar II packet from the concrete input packet. -/
theorem balaban_rg_uniform_lsi_pillar_ii_packet_of_concrete_input
    (d N_c : ℕ) [NeZero N_c]
    (input : BalabanRGUniformLSIConcreteInput d N_c) :
    BalabanRGUniformLSIPillarIIPacket d N_c := by
  exact
    balaban_rg_uniform_lsi_pillar_ii_packet_of_activation_data d N_c
      (balaban_rg_uniform_lsi_activation_data_of_concrete_input d N_c input)

/-- Canonical Pillar II packet from the obstruction packet. -/
theorem balaban_rg_uniform_lsi_pillar_ii_packet_of_obstruction_packet
    {d N_c : ℕ} [NeZero N_c]
    (packet : BalabanRGUniformLSIObstructionPacket d N_c) :
    BalabanRGUniformLSIPillarIIPacket d N_c := by
  exact
    balaban_rg_uniform_lsi_pillar_ii_packet_of_activation_data d N_c
      (activation_data_of_balaban_rg_uniform_lsi_obstruction_packet packet)

/-- Canonical Pillar II packet from the end-to-end packet. -/
theorem balaban_rg_uniform_lsi_pillar_ii_packet_of_end_to_end_packet
    {d N_c : ℕ} [NeZero N_c]
    (packet : BalabanRGUniformLSIEndToEndPacket d N_c) :
    BalabanRGUniformLSIPillarIIPacket d N_c := by
  exact
    balaban_rg_uniform_lsi_pillar_ii_packet_of_activation_data d N_c
      (activation_data_of_balaban_rg_uniform_lsi_end_to_end_packet packet)

/-- Projection to the abstract activation packet. -/
theorem activation_data_of_balaban_rg_uniform_lsi_pillar_ii_packet
    {d N_c : ℕ} [NeZero N_c]
    (packet : BalabanRGUniformLSIPillarIIPacket d N_c) :
    BalabanRGUniformLSIActivationData d N_c := by
  exact packet.activation

/-- Projection to the short public frontier. -/
theorem frontier_of_balaban_rg_uniform_lsi_pillar_ii_packet
    {d N_c : ℕ} [NeZero N_c]
    (packet : BalabanRGUniformLSIPillarIIPacket d N_c) :
    BalabanRGUniformLSIFrontier d N_c := by
  exact packet.frontier

/-- Projection to the direct input packet. -/
theorem direct_input_of_balaban_rg_uniform_lsi_pillar_ii_packet
    {d N_c : ℕ} [NeZero N_c]
    (packet : BalabanRGUniformLSIPillarIIPacket d N_c) :
    BalabanRGUniformLSIDirectInput d N_c := by
  exact packet.directInput

/-- Projection to the concrete input packet. -/
theorem concrete_input_of_balaban_rg_uniform_lsi_pillar_ii_packet
    {d N_c : ℕ} [NeZero N_c]
    (packet : BalabanRGUniformLSIPillarIIPacket d N_c) :
    BalabanRGUniformLSIConcreteInput d N_c := by
  exact packet.concreteInput

/-- Projection to the obstruction packet. -/
theorem obstruction_packet_of_balaban_rg_uniform_lsi_pillar_ii_packet
    {d N_c : ℕ} [NeZero N_c]
    (packet : BalabanRGUniformLSIPillarIIPacket d N_c) :
    BalabanRGUniformLSIObstructionPacket d N_c := by
  exact packet.obstruction

/-- Projection to the end-to-end packet. -/
theorem end_to_end_packet_of_balaban_rg_uniform_lsi_pillar_ii_packet
    {d N_c : ℕ} [NeZero N_c]
    (packet : BalabanRGUniformLSIPillarIIPacket d N_c) :
    BalabanRGUniformLSIEndToEndPacket d N_c := by
  exact packet.endToEnd

/-- Projection to the public facade. -/
theorem public_facade_of_balaban_rg_uniform_lsi_pillar_ii_packet
    {d N_c : ℕ} [NeZero N_c]
    (packet : BalabanRGUniformLSIPillarIIPacket d N_c) :
    BalabanRGUniformLSIPublicFacade d N_c := by
  exact packet.facade

/-- Projection to the structured closure package. -/
theorem closure_package_of_balaban_rg_uniform_lsi_pillar_ii_packet
    {d N_c : ℕ} [NeZero N_c]
    (packet : BalabanRGUniformLSIPillarIIPacket d N_c) :
    BalabanRGUniformLSIClosurePackage d N_c := by
  exact packet.closure

/-- Projection to the equivalence registry. -/
theorem equivalence_registry_of_balaban_rg_uniform_lsi_pillar_ii_packet
    {d N_c : ℕ} [NeZero N_c]
    (packet : BalabanRGUniformLSIPillarIIPacket d N_c) :
    BalabanRGUniformLSIEquivalenceRegistry d N_c := by
  exact packet.registry

/-- Projection to the packaged last-mile output. -/
theorem last_mile_output_of_balaban_rg_uniform_lsi_pillar_ii_packet
    {d N_c : ℕ} [NeZero N_c]
    (packet : BalabanRGUniformLSIPillarIIPacket d N_c) :
    BalabanRGUniformLSILastMileOutput d N_c := by
  exact packet.lastMile

/-- Projection to the transfer ingredient. -/
theorem transfer_of_balaban_rg_uniform_lsi_pillar_ii_packet
    {d N_c : ℕ} [NeZero N_c]
    (packet : BalabanRGUniformLSIPillarIIPacket d N_c) :
    HaarLSIFromUniformLSITransfer N_c := by
  exact packet.activation.transfer

/-- Projection to the preferred live target. -/
theorem live_target_of_balaban_rg_uniform_lsi_pillar_ii_packet
    {d N_c : ℕ} [NeZero N_c]
    (packet : BalabanRGUniformLSIPillarIIPacket d N_c) :
    BalabanRGUniformLSILiveTarget d N_c := by
  exact packet.activation.liveTarget

/-- Projection to the direct uniform-theorem target. -/
theorem direct_uniform_theorem_target_of_balaban_rg_uniform_lsi_pillar_ii_packet
    {d N_c : ℕ} [NeZero N_c]
    (packet : BalabanRGUniformLSIPillarIIPacket d N_c) :
    SpecialUnitaryDirectUniformLSITheoremTarget d N_c := by
  exact packet.obstruction.directTarget

/-- Projection to the old conditional target name. -/
theorem conditional_target_of_balaban_rg_uniform_lsi_pillar_ii_packet
    {d N_c : ℕ} [NeZero N_c]
    (packet : BalabanRGUniformLSIPillarIIPacket d N_c) :
    BalabanRGUniformLSIConditionalTarget d N_c := by
  exact packet.obstruction.conditionalTarget

/-- Projection to the old Haar-lane live target name. -/
theorem haar_lsi_live_target_of_balaban_rg_uniform_lsi_pillar_ii_packet
    {d N_c : ℕ} [NeZero N_c]
    (packet : BalabanRGUniformLSIPillarIIPacket d N_c) :
    HaarLSILiveTarget d N_c := by
  exact packet.obstruction.haarLiveTarget

/-- Projection to the bare package-witness surface. -/
theorem pkg_witness_of_balaban_rg_uniform_lsi_pillar_ii_packet
    {d N_c : ℕ} [NeZero N_c]
    (packet : BalabanRGUniformLSIPillarIIPacket d N_c) :
    ∃ _ : BalabanRGPackage d N_c, True := by
  exact packet.obstruction.pkgWitness

/-- Projection to the scale target. -/
theorem scale_target_of_balaban_rg_uniform_lsi_pillar_ii_packet
    {d N_c : ℕ} [NeZero N_c]
    (packet : BalabanRGUniformLSIPillarIIPacket d N_c) :
    SpecialUnitaryScaleLSITarget d N_c := by
  exact packet.closure.scaleTarget

/-- Projection to the Haar target. -/
theorem haar_target_of_balaban_rg_uniform_lsi_pillar_ii_packet
    {d N_c : ℕ} [NeZero N_c]
    (packet : BalabanRGUniformLSIPillarIIPacket d N_c) :
    HaarLSITarget N_c := by
  exact packet.closure.haarTarget

/-- Projection to the frontier package. -/
theorem frontier_package_of_balaban_rg_uniform_lsi_pillar_ii_packet
    {d N_c : ℕ} [NeZero N_c]
    (packet : BalabanRGUniformLSIPillarIIPacket d N_c) :
    HaarLSIFrontierPackage d N_c := by
  exact packet.closure.frontierPackage

/-- Logical normal form: the Pillar II packet is equivalent to the abstract activation packet. -/
theorem balaban_rg_uniform_lsi_pillar_ii_packet_iff_activation_data
    (d N_c : ℕ) [NeZero N_c] :
    BalabanRGUniformLSIPillarIIPacket d N_c ↔
      BalabanRGUniformLSIActivationData d N_c := by
  constructor
  · intro packet
    exact packet.activation
  · intro data
    exact balaban_rg_uniform_lsi_pillar_ii_packet_of_activation_data d N_c data

/-- Logical normal form: the Pillar II packet is equivalent to the direct input packet. -/
theorem balaban_rg_uniform_lsi_pillar_ii_packet_iff_direct_input
    (d N_c : ℕ) [NeZero N_c] :
    BalabanRGUniformLSIPillarIIPacket d N_c ↔
      BalabanRGUniformLSIDirectInput d N_c := by
  constructor
  · intro packet
    exact packet.directInput
  · intro input
    exact balaban_rg_uniform_lsi_pillar_ii_packet_of_direct_input d N_c input

/-- Logical normal form: the Pillar II packet is equivalent to the concrete input packet. -/
theorem balaban_rg_uniform_lsi_pillar_ii_packet_iff_concrete_input
    (d N_c : ℕ) [NeZero N_c] :
    BalabanRGUniformLSIPillarIIPacket d N_c ↔
      BalabanRGUniformLSIConcreteInput d N_c := by
  constructor
  · intro packet
    exact packet.concreteInput
  · intro input
    exact balaban_rg_uniform_lsi_pillar_ii_packet_of_concrete_input d N_c input

/-- Logical normal form: the Pillar II packet is equivalent to the short public frontier. -/
theorem balaban_rg_uniform_lsi_pillar_ii_packet_iff_frontier
    (d N_c : ℕ) [NeZero N_c] :
    BalabanRGUniformLSIPillarIIPacket d N_c ↔
      BalabanRGUniformLSIFrontier d N_c := by
  constructor
  · intro packet
    exact packet.frontier
  · intro frontier
    exact balaban_rg_uniform_lsi_pillar_ii_packet_of_frontier frontier

/-- Logical normal form: the Pillar II packet is equivalent to the obstruction packet. -/
theorem balaban_rg_uniform_lsi_pillar_ii_packet_iff_obstruction_packet
    (d N_c : ℕ) [NeZero N_c] :
    BalabanRGUniformLSIPillarIIPacket d N_c ↔
      BalabanRGUniformLSIObstructionPacket d N_c := by
  constructor
  · intro packet
    exact packet.obstruction
  · intro obstruction
    exact balaban_rg_uniform_lsi_pillar_ii_packet_of_obstruction_packet obstruction

/-- Logical normal form: the Pillar II packet is equivalent to the end-to-end packet. -/
theorem balaban_rg_uniform_lsi_pillar_ii_packet_iff_end_to_end_packet
    (d N_c : ℕ) [NeZero N_c] :
    BalabanRGUniformLSIPillarIIPacket d N_c ↔
      BalabanRGUniformLSIEndToEndPacket d N_c := by
  constructor
  · intro packet
    exact packet.endToEnd
  · intro e2e
    exact balaban_rg_uniform_lsi_pillar_ii_packet_of_end_to_end_packet e2e

/-- Coherence: the Pillar II packet is propositionally equal to the canonical one reconstructed from its activation data. -/
theorem balaban_rg_uniform_lsi_pillar_ii_packet_eq_canonical_of_activation_data
    {d N_c : ℕ} [NeZero N_c]
    (packet : BalabanRGUniformLSIPillarIIPacket d N_c) :
    packet =
      balaban_rg_uniform_lsi_pillar_ii_packet_of_activation_data d N_c
        (activation_data_of_balaban_rg_uniform_lsi_pillar_ii_packet packet) := by
  apply Subsingleton.elim

/-- Round-trip coherence: frontier → Pillar II → frontier is canonically the identity. -/
theorem balaban_rg_uniform_lsi_frontier_of_pillar_ii_packet_of_frontier_eq_canonical
    {d N_c : ℕ} [NeZero N_c]
    (frontier : BalabanRGUniformLSIFrontier d N_c) :
    frontier_of_balaban_rg_uniform_lsi_pillar_ii_packet
      (balaban_rg_uniform_lsi_pillar_ii_packet_of_frontier frontier) = frontier := by
  apply Subsingleton.elim

/-- Round-trip coherence: direct input → Pillar II → direct input is canonically the identity. -/
theorem balaban_rg_uniform_lsi_direct_input_of_pillar_ii_packet_of_direct_input_eq_canonical
    {d N_c : ℕ} [NeZero N_c]
    (input : BalabanRGUniformLSIDirectInput d N_c) :
    direct_input_of_balaban_rg_uniform_lsi_pillar_ii_packet
      (balaban_rg_uniform_lsi_pillar_ii_packet_of_direct_input d N_c input) = input := by
  apply Subsingleton.elim

/-- Round-trip coherence: concrete input → Pillar II → concrete input is canonically the identity. -/
theorem balaban_rg_uniform_lsi_concrete_input_of_pillar_ii_packet_of_concrete_input_eq_canonical
    {d N_c : ℕ} [NeZero N_c]
    (input : BalabanRGUniformLSIConcreteInput d N_c) :
    concrete_input_of_balaban_rg_uniform_lsi_pillar_ii_packet
      (balaban_rg_uniform_lsi_pillar_ii_packet_of_concrete_input d N_c input) = input := by
  apply Subsingleton.elim

/-- Round-trip coherence: obstruction → Pillar II → obstruction is canonically the identity. -/
theorem balaban_rg_uniform_lsi_obstruction_packet_of_pillar_ii_packet_of_obstruction_packet_eq_canonical
    {d N_c : ℕ} [NeZero N_c]
    (packet : BalabanRGUniformLSIObstructionPacket d N_c) :
    obstruction_packet_of_balaban_rg_uniform_lsi_pillar_ii_packet
      (balaban_rg_uniform_lsi_pillar_ii_packet_of_obstruction_packet packet) = packet := by
  apply Subsingleton.elim

/-- Round-trip coherence: end-to-end → Pillar II → end-to-end is canonically the identity. -/
theorem balaban_rg_uniform_lsi_end_to_end_packet_of_pillar_ii_packet_of_end_to_end_packet_eq_canonical
    {d N_c : ℕ} [NeZero N_c]
    (packet : BalabanRGUniformLSIEndToEndPacket d N_c) :
    end_to_end_packet_of_balaban_rg_uniform_lsi_pillar_ii_packet
      (balaban_rg_uniform_lsi_pillar_ii_packet_of_end_to_end_packet packet) = packet := by
  apply Subsingleton.elim

end YangMills.ClayCore
