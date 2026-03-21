import Mathlib
import YangMills.ClayCore.BalabanRG.BalabanRGUniformLSIInputCoherence

namespace YangMills.ClayCore

/-- Unified public omnibus packet for the current Balaban-RG / Haar-LSI lane:
it carries the currently exported input and output surfaces together. -/
structure BalabanRGUniformLSIEndToEndPacket (d N_c : ℕ) [NeZero N_c] : Prop where
  activation : BalabanRGUniformLSIActivationData d N_c
  directInput : BalabanRGUniformLSIDirectInput d N_c
  concreteInput : BalabanRGUniformLSIConcreteInput d N_c
  frontier : BalabanRGUniformLSIFrontier d N_c
  facade : BalabanRGUniformLSIPublicFacade d N_c
  closure : BalabanRGUniformLSIClosurePackage d N_c
  registry : BalabanRGUniformLSIEquivalenceRegistry d N_c
  lastMile : BalabanRGUniformLSILastMileOutput d N_c

/-- Canonical omnibus packet from the abstract activation packet. -/
theorem balaban_rg_uniform_lsi_end_to_end_packet_of_activation_data
    (d N_c : ℕ) [NeZero N_c]
    (data : BalabanRGUniformLSIActivationData d N_c) :
    BalabanRGUniformLSIEndToEndPacket d N_c := by
  let frontier : BalabanRGUniformLSIFrontier d N_c :=
    balaban_rg_uniform_lsi_frontier_of_activation_data d N_c data
  exact
    { activation := data
      directInput := balaban_rg_uniform_lsi_direct_input_of_activation_data data
      concreteInput := balaban_rg_uniform_lsi_concrete_input_of_activation_data data
      frontier := frontier
      facade := public_facade_of_balaban_rg_uniform_lsi_frontier frontier
      closure := closure_package_of_balaban_rg_uniform_lsi_frontier frontier
      registry := equivalence_registry_of_balaban_rg_uniform_lsi_frontier frontier
      lastMile := last_mile_output_of_balaban_rg_uniform_lsi_frontier frontier }

/-- Canonical omnibus packet from the direct input packet. -/
theorem balaban_rg_uniform_lsi_end_to_end_packet_of_direct_input
    (d N_c : ℕ) [NeZero N_c]
    (input : BalabanRGUniformLSIDirectInput d N_c) :
    BalabanRGUniformLSIEndToEndPacket d N_c := by
  exact
    balaban_rg_uniform_lsi_end_to_end_packet_of_activation_data d N_c
      (activation_data_of_balaban_rg_uniform_lsi_direct_input d N_c input)

/-- Canonical omnibus packet from the concrete input packet. -/
theorem balaban_rg_uniform_lsi_end_to_end_packet_of_concrete_input
    (d N_c : ℕ) [NeZero N_c]
    (input : BalabanRGUniformLSIConcreteInput d N_c) :
    BalabanRGUniformLSIEndToEndPacket d N_c := by
  exact
    balaban_rg_uniform_lsi_end_to_end_packet_of_activation_data d N_c
      (balaban_rg_uniform_lsi_activation_data_of_concrete_input d N_c input)

/-- Canonical omnibus packet from the short public frontier. -/
theorem balaban_rg_uniform_lsi_end_to_end_packet_of_frontier
    {d N_c : ℕ} [NeZero N_c]
    (frontier : BalabanRGUniformLSIFrontier d N_c) :
    BalabanRGUniformLSIEndToEndPacket d N_c := by
  exact
    balaban_rg_uniform_lsi_end_to_end_packet_of_activation_data d N_c
      (activation_data_of_balaban_rg_uniform_lsi_frontier frontier)

/-- Projection to the abstract activation packet. -/
theorem activation_data_of_balaban_rg_uniform_lsi_end_to_end_packet
    {d N_c : ℕ} [NeZero N_c]
    (packet : BalabanRGUniformLSIEndToEndPacket d N_c) :
    BalabanRGUniformLSIActivationData d N_c := by
  exact packet.activation

/-- Projection to the direct input packet. -/
theorem direct_input_of_balaban_rg_uniform_lsi_end_to_end_packet
    {d N_c : ℕ} [NeZero N_c]
    (packet : BalabanRGUniformLSIEndToEndPacket d N_c) :
    BalabanRGUniformLSIDirectInput d N_c := by
  exact packet.directInput

/-- Projection to the concrete input packet. -/
theorem concrete_input_of_balaban_rg_uniform_lsi_end_to_end_packet
    {d N_c : ℕ} [NeZero N_c]
    (packet : BalabanRGUniformLSIEndToEndPacket d N_c) :
    BalabanRGUniformLSIConcreteInput d N_c := by
  exact packet.concreteInput

/-- Projection to the short public frontier. -/
theorem frontier_of_balaban_rg_uniform_lsi_end_to_end_packet
    {d N_c : ℕ} [NeZero N_c]
    (packet : BalabanRGUniformLSIEndToEndPacket d N_c) :
    BalabanRGUniformLSIFrontier d N_c := by
  exact packet.frontier

/-- Projection to the public facade. -/
theorem public_facade_of_balaban_rg_uniform_lsi_end_to_end_packet
    {d N_c : ℕ} [NeZero N_c]
    (packet : BalabanRGUniformLSIEndToEndPacket d N_c) :
    BalabanRGUniformLSIPublicFacade d N_c := by
  exact packet.facade

/-- Projection to the closure package. -/
theorem closure_package_of_balaban_rg_uniform_lsi_end_to_end_packet
    {d N_c : ℕ} [NeZero N_c]
    (packet : BalabanRGUniformLSIEndToEndPacket d N_c) :
    BalabanRGUniformLSIClosurePackage d N_c := by
  exact packet.closure

/-- Projection to the equivalence registry. -/
theorem equivalence_registry_of_balaban_rg_uniform_lsi_end_to_end_packet
    {d N_c : ℕ} [NeZero N_c]
    (packet : BalabanRGUniformLSIEndToEndPacket d N_c) :
    BalabanRGUniformLSIEquivalenceRegistry d N_c := by
  exact packet.registry

/-- Projection to the packaged last-mile output. -/
theorem last_mile_output_of_balaban_rg_uniform_lsi_end_to_end_packet
    {d N_c : ℕ} [NeZero N_c]
    (packet : BalabanRGUniformLSIEndToEndPacket d N_c) :
    BalabanRGUniformLSILastMileOutput d N_c := by
  exact packet.lastMile

/-- Projection to the transfer ingredient. -/
theorem transfer_of_balaban_rg_uniform_lsi_end_to_end_packet
    {d N_c : ℕ} [NeZero N_c]
    (packet : BalabanRGUniformLSIEndToEndPacket d N_c) :
    HaarLSIFromUniformLSITransfer N_c := by
  exact packet.activation.transfer

/-- Projection to the preferred live target. -/
theorem live_target_of_balaban_rg_uniform_lsi_end_to_end_packet
    {d N_c : ℕ} [NeZero N_c]
    (packet : BalabanRGUniformLSIEndToEndPacket d N_c) :
    BalabanRGUniformLSILiveTarget d N_c := by
  exact packet.activation.liveTarget

/-- Projection to the direct uniform-theorem target. -/
theorem direct_uniform_theorem_target_of_balaban_rg_uniform_lsi_end_to_end_packet
    {d N_c : ℕ} [NeZero N_c]
    (packet : BalabanRGUniformLSIEndToEndPacket d N_c) :
    SpecialUnitaryDirectUniformLSITheoremTarget d N_c := by
  exact direct_uniform_theorem_target_of_balaban_rg_uniform_lsi_direct_input packet.directInput

/-- Projection to the bare package-witness surface. -/
theorem pkg_witness_of_balaban_rg_uniform_lsi_end_to_end_packet
    {d N_c : ℕ} [NeZero N_c]
    (packet : BalabanRGUniformLSIEndToEndPacket d N_c) :
    ∃ _ : BalabanRGPackage d N_c, True := by
  exact pkg_witness_of_balaban_rg_uniform_lsi_concrete_input packet.concreteInput

/-- Logical normal form: the omnibus packet is equivalent to the abstract activation packet. -/
theorem balaban_rg_uniform_lsi_end_to_end_packet_iff_activation_data
    (d N_c : ℕ) [NeZero N_c] :
    BalabanRGUniformLSIEndToEndPacket d N_c ↔
      BalabanRGUniformLSIActivationData d N_c := by
  constructor
  · intro packet
    exact packet.activation
  · intro data
    exact balaban_rg_uniform_lsi_end_to_end_packet_of_activation_data d N_c data

/-- Logical normal form: the omnibus packet is equivalent to the direct input packet. -/
theorem balaban_rg_uniform_lsi_end_to_end_packet_iff_direct_input
    (d N_c : ℕ) [NeZero N_c] :
    BalabanRGUniformLSIEndToEndPacket d N_c ↔
      BalabanRGUniformLSIDirectInput d N_c := by
  constructor
  · intro packet
    exact packet.directInput
  · intro input
    exact balaban_rg_uniform_lsi_end_to_end_packet_of_direct_input d N_c input

/-- Logical normal form: the omnibus packet is equivalent to the concrete input packet. -/
theorem balaban_rg_uniform_lsi_end_to_end_packet_iff_concrete_input
    (d N_c : ℕ) [NeZero N_c] :
    BalabanRGUniformLSIEndToEndPacket d N_c ↔
      BalabanRGUniformLSIConcreteInput d N_c := by
  constructor
  · intro packet
    exact packet.concreteInput
  · intro input
    exact balaban_rg_uniform_lsi_end_to_end_packet_of_concrete_input d N_c input

/-- Logical normal form: the omnibus packet is equivalent to the short public frontier. -/
theorem balaban_rg_uniform_lsi_end_to_end_packet_iff_frontier
    (d N_c : ℕ) [NeZero N_c] :
    BalabanRGUniformLSIEndToEndPacket d N_c ↔
      BalabanRGUniformLSIFrontier d N_c := by
  constructor
  · intro packet
    exact packet.frontier
  · intro frontier
    exact balaban_rg_uniform_lsi_end_to_end_packet_of_frontier frontier

/-- Coherence: the omnibus packet is propositionally equal to the canonical one reconstructed from its activation data. -/
theorem balaban_rg_uniform_lsi_end_to_end_packet_eq_canonical_of_activation_data
    {d N_c : ℕ} [NeZero N_c]
    (packet : BalabanRGUniformLSIEndToEndPacket d N_c) :
    packet =
      balaban_rg_uniform_lsi_end_to_end_packet_of_activation_data d N_c
        (activation_data_of_balaban_rg_uniform_lsi_end_to_end_packet packet) := by
  apply Subsingleton.elim

/-- Round-trip coherence: activation → packet → activation is canonically the identity. -/
theorem balaban_rg_uniform_lsi_activation_data_of_end_to_end_packet_of_activation_data_eq_canonical
    {d N_c : ℕ} [NeZero N_c]
    (data : BalabanRGUniformLSIActivationData d N_c) :
    activation_data_of_balaban_rg_uniform_lsi_end_to_end_packet
      (balaban_rg_uniform_lsi_end_to_end_packet_of_activation_data d N_c data) = data := by
  rfl

/-- Round-trip coherence: direct input → packet → direct input is canonically the identity. -/
theorem balaban_rg_uniform_lsi_direct_input_of_end_to_end_packet_of_direct_input_eq_canonical
    {d N_c : ℕ} [NeZero N_c]
    (input : BalabanRGUniformLSIDirectInput d N_c) :
    direct_input_of_balaban_rg_uniform_lsi_end_to_end_packet
      (balaban_rg_uniform_lsi_end_to_end_packet_of_direct_input d N_c input) = input := by
  apply Subsingleton.elim

/-- Round-trip coherence: concrete input → packet → concrete input is canonically the identity. -/
theorem balaban_rg_uniform_lsi_concrete_input_of_end_to_end_packet_of_concrete_input_eq_canonical
    {d N_c : ℕ} [NeZero N_c]
    (input : BalabanRGUniformLSIConcreteInput d N_c) :
    concrete_input_of_balaban_rg_uniform_lsi_end_to_end_packet
      (balaban_rg_uniform_lsi_end_to_end_packet_of_concrete_input d N_c input) = input := by
  apply Subsingleton.elim

/-- Round-trip coherence: frontier → packet → frontier is canonically the identity. -/
theorem balaban_rg_uniform_lsi_frontier_of_end_to_end_packet_of_frontier_eq_canonical
    {d N_c : ℕ} [NeZero N_c]
    (frontier : BalabanRGUniformLSIFrontier d N_c) :
    frontier_of_balaban_rg_uniform_lsi_end_to_end_packet
      (balaban_rg_uniform_lsi_end_to_end_packet_of_frontier frontier) = frontier := by
  apply Subsingleton.elim

end YangMills.ClayCore
