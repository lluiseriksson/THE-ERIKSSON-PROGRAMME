import Mathlib
import YangMills.ClayCore.BalabanRG.BalabanRGUniformLSIEndToEndPacket

namespace YangMills.ClayCore

/-- Canonical packet exposing the still-live obstruction surface for the current
Balaban-RG / Haar-LSI lane under all currently equivalent public names. -/
structure BalabanRGUniformLSIObstructionPacket (d N_c : ℕ) [NeZero N_c] : Prop where
  transfer : HaarLSIFromUniformLSITransfer N_c
  liveTarget : BalabanRGUniformLSILiveTarget d N_c
  directTarget : SpecialUnitaryDirectUniformLSITheoremTarget d N_c
  conditionalTarget : BalabanRGUniformLSIConditionalTarget d N_c
  haarLiveTarget : HaarLSILiveTarget d N_c
  pkgWitness : ∃ _ : BalabanRGPackage d N_c, True

/-- Canonical obstruction packet from the abstract activation packet. -/
theorem balaban_rg_uniform_lsi_obstruction_packet_of_activation_data
    (d N_c : ℕ) [NeZero N_c]
    (data : BalabanRGUniformLSIActivationData d N_c) :
    BalabanRGUniformLSIObstructionPacket d N_c := by
  exact
    { transfer := data.transfer
      liveTarget := data.liveTarget
      directTarget := direct_uniform_theorem_target_of_activation_data data
      conditionalTarget := conditional_target_of_activation_data data
      haarLiveTarget := haar_lsi_live_target_of_activation_data data
      pkgWitness := pkg_witness_of_activation_data data }

/-- Canonical obstruction packet from the preferred live target. -/
theorem balaban_rg_uniform_lsi_obstruction_packet_of_live_target
    (d N_c : ℕ) [NeZero N_c]
    (tr : HaarLSIFromUniformLSITransfer N_c)
    (h : BalabanRGUniformLSILiveTarget d N_c) :
    BalabanRGUniformLSIObstructionPacket d N_c := by
  exact
    balaban_rg_uniform_lsi_obstruction_packet_of_activation_data d N_c
      (balaban_rg_uniform_lsi_activation_data_of_live_target d N_c tr h)

/-- Canonical obstruction packet from the direct input packet. -/
theorem balaban_rg_uniform_lsi_obstruction_packet_of_direct_input
    (d N_c : ℕ) [NeZero N_c]
    (input : BalabanRGUniformLSIDirectInput d N_c) :
    BalabanRGUniformLSIObstructionPacket d N_c := by
  exact
    balaban_rg_uniform_lsi_obstruction_packet_of_activation_data d N_c
      (activation_data_of_balaban_rg_uniform_lsi_direct_input d N_c input)

/-- Canonical obstruction packet from the concrete input packet. -/
theorem balaban_rg_uniform_lsi_obstruction_packet_of_concrete_input
    (d N_c : ℕ) [NeZero N_c]
    (input : BalabanRGUniformLSIConcreteInput d N_c) :
    BalabanRGUniformLSIObstructionPacket d N_c := by
  exact
    balaban_rg_uniform_lsi_obstruction_packet_of_activation_data d N_c
      (balaban_rg_uniform_lsi_activation_data_of_concrete_input d N_c input)

/-- Canonical obstruction packet from the short public frontier. -/
theorem balaban_rg_uniform_lsi_obstruction_packet_of_frontier
    {d N_c : ℕ} [NeZero N_c]
    (frontier : BalabanRGUniformLSIFrontier d N_c) :
    BalabanRGUniformLSIObstructionPacket d N_c := by
  exact
    balaban_rg_uniform_lsi_obstruction_packet_of_activation_data d N_c
      (activation_data_of_balaban_rg_uniform_lsi_frontier frontier)

/-- Canonical obstruction packet from the unified end-to-end packet. -/
theorem balaban_rg_uniform_lsi_obstruction_packet_of_end_to_end_packet
    {d N_c : ℕ} [NeZero N_c]
    (packet : BalabanRGUniformLSIEndToEndPacket d N_c) :
    BalabanRGUniformLSIObstructionPacket d N_c := by
  exact
    balaban_rg_uniform_lsi_obstruction_packet_of_activation_data d N_c
      (activation_data_of_balaban_rg_uniform_lsi_end_to_end_packet packet)

/-- Canonical obstruction packet from an actual Balaban-RG package witness. -/
theorem balaban_rg_uniform_lsi_obstruction_packet_of_pkg
    (d N_c : ℕ) [NeZero N_c]
    (tr : HaarLSIFromUniformLSITransfer N_c)
    (pkg : BalabanRGPackage d N_c) :
    BalabanRGUniformLSIObstructionPacket d N_c := by
  exact
    balaban_rg_uniform_lsi_obstruction_packet_of_activation_data d N_c
      (balaban_rg_uniform_lsi_activation_data_of_pkg d N_c tr pkg)

/-- Canonical obstruction packet from the bare package-witness surface. -/
theorem balaban_rg_uniform_lsi_obstruction_packet_of_pkg_witness
    (d N_c : ℕ) [NeZero N_c]
    (tr : HaarLSIFromUniformLSITransfer N_c)
    (h : ∃ _ : BalabanRGPackage d N_c, True) :
    BalabanRGUniformLSIObstructionPacket d N_c := by
  exact
    balaban_rg_uniform_lsi_obstruction_packet_of_activation_data d N_c
      (balaban_rg_uniform_lsi_activation_data_of_pkg_witness d N_c tr h)

/-- Projection to the abstract activation packet. -/
theorem activation_data_of_balaban_rg_uniform_lsi_obstruction_packet
    {d N_c : ℕ} [NeZero N_c]
    (packet : BalabanRGUniformLSIObstructionPacket d N_c) :
    BalabanRGUniformLSIActivationData d N_c := by
  exact
    balaban_rg_uniform_lsi_activation_data_of_live_target
      d N_c packet.transfer packet.liveTarget

/-- Projection to the short public frontier. -/
theorem frontier_of_balaban_rg_uniform_lsi_obstruction_packet
    {d N_c : ℕ} [NeZero N_c]
    (packet : BalabanRGUniformLSIObstructionPacket d N_c) :
    BalabanRGUniformLSIFrontier d N_c := by
  exact
    balaban_rg_uniform_lsi_frontier_of_live_target
      d N_c packet.transfer packet.liveTarget

/-- Projection to the direct input packet. -/
theorem direct_input_of_balaban_rg_uniform_lsi_obstruction_packet
    {d N_c : ℕ} [NeZero N_c]
    (packet : BalabanRGUniformLSIObstructionPacket d N_c) :
    BalabanRGUniformLSIDirectInput d N_c := by
  exact
    balaban_rg_uniform_lsi_direct_input_of_activation_data
      (activation_data_of_balaban_rg_uniform_lsi_obstruction_packet packet)

/-- Projection to the concrete input packet. -/
theorem concrete_input_of_balaban_rg_uniform_lsi_obstruction_packet
    {d N_c : ℕ} [NeZero N_c]
    (packet : BalabanRGUniformLSIObstructionPacket d N_c) :
    BalabanRGUniformLSIConcreteInput d N_c := by
  exact
    balaban_rg_uniform_lsi_concrete_input_of_activation_data
      (activation_data_of_balaban_rg_uniform_lsi_obstruction_packet packet)

/-- Projection to the unified end-to-end packet. -/
theorem end_to_end_packet_of_balaban_rg_uniform_lsi_obstruction_packet
    {d N_c : ℕ} [NeZero N_c]
    (packet : BalabanRGUniformLSIObstructionPacket d N_c) :
    BalabanRGUniformLSIEndToEndPacket d N_c := by
  exact
    balaban_rg_uniform_lsi_end_to_end_packet_of_activation_data d N_c
      (activation_data_of_balaban_rg_uniform_lsi_obstruction_packet packet)

/-- Projection to the public facade. -/
theorem public_facade_of_balaban_rg_uniform_lsi_obstruction_packet
    {d N_c : ℕ} [NeZero N_c]
    (packet : BalabanRGUniformLSIObstructionPacket d N_c) :
    BalabanRGUniformLSIPublicFacade d N_c := by
  exact
    balaban_rg_uniform_lsi_public_facade_of_activation_data d N_c
      (activation_data_of_balaban_rg_uniform_lsi_obstruction_packet packet)

/-- Projection to the structured closure package. -/
theorem closure_package_of_balaban_rg_uniform_lsi_obstruction_packet
    {d N_c : ℕ} [NeZero N_c]
    (packet : BalabanRGUniformLSIObstructionPacket d N_c) :
    BalabanRGUniformLSIClosurePackage d N_c := by
  exact
    balaban_rg_uniform_lsi_closure_package_of_activation_data d N_c
      (activation_data_of_balaban_rg_uniform_lsi_obstruction_packet packet)

/-- Projection to the equivalence registry. -/
theorem equivalence_registry_of_balaban_rg_uniform_lsi_obstruction_packet
    {d N_c : ℕ} [NeZero N_c]
    (packet : BalabanRGUniformLSIObstructionPacket d N_c) :
    BalabanRGUniformLSIEquivalenceRegistry d N_c := by
  exact
    balaban_rg_uniform_lsi_equivalence_registry_of_activation_data d N_c
      (activation_data_of_balaban_rg_uniform_lsi_obstruction_packet packet)

/-- Projection to the bundled last-mile output. -/
theorem last_mile_output_of_balaban_rg_uniform_lsi_obstruction_packet
    {d N_c : ℕ} [NeZero N_c]
    (packet : BalabanRGUniformLSIObstructionPacket d N_c) :
    BalabanRGUniformLSILastMileOutput d N_c := by
  exact
    balaban_rg_uniform_lsi_last_mile_output_of_activation_data d N_c
      (activation_data_of_balaban_rg_uniform_lsi_obstruction_packet packet)

/-- Projection to the scale target. -/
theorem scale_target_of_balaban_rg_uniform_lsi_obstruction_packet
    {d N_c : ℕ} [NeZero N_c]
    (packet : BalabanRGUniformLSIObstructionPacket d N_c) :
    SpecialUnitaryScaleLSITarget d N_c := by
  exact
    scale_target_of_activation_data
      (activation_data_of_balaban_rg_uniform_lsi_obstruction_packet packet)

/-- Projection to the Haar target. -/
theorem haar_target_of_balaban_rg_uniform_lsi_obstruction_packet
    {d N_c : ℕ} [NeZero N_c]
    (packet : BalabanRGUniformLSIObstructionPacket d N_c) :
    HaarLSITarget N_c := by
  exact
    haar_target_of_activation_data
      (activation_data_of_balaban_rg_uniform_lsi_obstruction_packet packet)

/-- Projection to the frontier package. -/
theorem frontier_package_of_balaban_rg_uniform_lsi_obstruction_packet
    {d N_c : ℕ} [NeZero N_c]
    (packet : BalabanRGUniformLSIObstructionPacket d N_c) :
    HaarLSIFrontierPackage d N_c := by
  exact
    frontier_package_of_activation_data
      (activation_data_of_balaban_rg_uniform_lsi_obstruction_packet packet)

/-- Logical normal form: the obstruction packet is equivalent to the abstract activation packet. -/
theorem balaban_rg_uniform_lsi_obstruction_packet_iff_activation_data
    (d N_c : ℕ) [NeZero N_c] :
    BalabanRGUniformLSIObstructionPacket d N_c ↔
      BalabanRGUniformLSIActivationData d N_c := by
  constructor
  · intro packet
    exact activation_data_of_balaban_rg_uniform_lsi_obstruction_packet packet
  · intro data
    exact balaban_rg_uniform_lsi_obstruction_packet_of_activation_data d N_c data

/-- Logical normal form: the obstruction packet is equivalent to the direct input packet. -/
theorem balaban_rg_uniform_lsi_obstruction_packet_iff_direct_input
    (d N_c : ℕ) [NeZero N_c] :
    BalabanRGUniformLSIObstructionPacket d N_c ↔
      BalabanRGUniformLSIDirectInput d N_c := by
  constructor
  · intro packet
    exact direct_input_of_balaban_rg_uniform_lsi_obstruction_packet packet
  · intro input
    exact balaban_rg_uniform_lsi_obstruction_packet_of_direct_input d N_c input

/-- Logical normal form: the obstruction packet is equivalent to the concrete input packet. -/
theorem balaban_rg_uniform_lsi_obstruction_packet_iff_concrete_input
    (d N_c : ℕ) [NeZero N_c] :
    BalabanRGUniformLSIObstructionPacket d N_c ↔
      BalabanRGUniformLSIConcreteInput d N_c := by
  constructor
  · intro packet
    exact concrete_input_of_balaban_rg_uniform_lsi_obstruction_packet packet
  · intro input
    exact balaban_rg_uniform_lsi_obstruction_packet_of_concrete_input d N_c input

/-- Logical normal form: the obstruction packet is equivalent to the short public frontier. -/
theorem balaban_rg_uniform_lsi_obstruction_packet_iff_frontier
    (d N_c : ℕ) [NeZero N_c] :
    BalabanRGUniformLSIObstructionPacket d N_c ↔
      BalabanRGUniformLSIFrontier d N_c := by
  constructor
  · intro packet
    exact frontier_of_balaban_rg_uniform_lsi_obstruction_packet packet
  · intro frontier
    exact balaban_rg_uniform_lsi_obstruction_packet_of_frontier frontier

/-- Logical normal form: the obstruction packet is equivalent to the unified end-to-end packet. -/
theorem balaban_rg_uniform_lsi_obstruction_packet_iff_end_to_end_packet
    (d N_c : ℕ) [NeZero N_c] :
    BalabanRGUniformLSIObstructionPacket d N_c ↔
      BalabanRGUniformLSIEndToEndPacket d N_c := by
  constructor
  · intro packet
    exact end_to_end_packet_of_balaban_rg_uniform_lsi_obstruction_packet packet
  · intro e2e
    exact balaban_rg_uniform_lsi_obstruction_packet_of_end_to_end_packet e2e

/-- Coherence: the obstruction packet is propositionally equal to the canonical one reconstructed from its activation data. -/
theorem balaban_rg_uniform_lsi_obstruction_packet_eq_canonical_of_activation_data
    {d N_c : ℕ} [NeZero N_c]
    (packet : BalabanRGUniformLSIObstructionPacket d N_c) :
    packet =
      balaban_rg_uniform_lsi_obstruction_packet_of_activation_data d N_c
        (activation_data_of_balaban_rg_uniform_lsi_obstruction_packet packet) := by
  apply Subsingleton.elim

/-- Round-trip coherence: activation → obstruction → activation is canonically the identity. -/
theorem balaban_rg_uniform_lsi_activation_data_of_obstruction_packet_of_activation_data_eq_canonical
    {d N_c : ℕ} [NeZero N_c]
    (data : BalabanRGUniformLSIActivationData d N_c) :
    activation_data_of_balaban_rg_uniform_lsi_obstruction_packet
      (balaban_rg_uniform_lsi_obstruction_packet_of_activation_data d N_c data) = data := by
  apply Subsingleton.elim

/-- Round-trip coherence: frontier → obstruction → frontier is canonically the identity. -/
theorem balaban_rg_uniform_lsi_frontier_of_obstruction_packet_of_frontier_eq_canonical
    {d N_c : ℕ} [NeZero N_c]
    (frontier : BalabanRGUniformLSIFrontier d N_c) :
    frontier_of_balaban_rg_uniform_lsi_obstruction_packet
      (balaban_rg_uniform_lsi_obstruction_packet_of_frontier frontier) = frontier := by
  apply Subsingleton.elim

/-- Round-trip coherence: direct input → obstruction → direct input is canonically the identity. -/
theorem balaban_rg_uniform_lsi_direct_input_of_obstruction_packet_of_direct_input_eq_canonical
    {d N_c : ℕ} [NeZero N_c]
    (input : BalabanRGUniformLSIDirectInput d N_c) :
    direct_input_of_balaban_rg_uniform_lsi_obstruction_packet
      (balaban_rg_uniform_lsi_obstruction_packet_of_direct_input d N_c input) = input := by
  apply Subsingleton.elim

/-- Round-trip coherence: concrete input → obstruction → concrete input is canonically the identity. -/
theorem balaban_rg_uniform_lsi_concrete_input_of_obstruction_packet_of_concrete_input_eq_canonical
    {d N_c : ℕ} [NeZero N_c]
    (input : BalabanRGUniformLSIConcreteInput d N_c) :
    concrete_input_of_balaban_rg_uniform_lsi_obstruction_packet
      (balaban_rg_uniform_lsi_obstruction_packet_of_concrete_input d N_c input) = input := by
  apply Subsingleton.elim

/-- Round-trip coherence: end-to-end packet → obstruction → end-to-end packet is canonically the identity. -/
theorem balaban_rg_uniform_lsi_end_to_end_packet_of_obstruction_packet_of_end_to_end_packet_eq_canonical
    {d N_c : ℕ} [NeZero N_c]
    (packet : BalabanRGUniformLSIEndToEndPacket d N_c) :
    end_to_end_packet_of_balaban_rg_uniform_lsi_obstruction_packet
      (balaban_rg_uniform_lsi_obstruction_packet_of_end_to_end_packet packet) = packet := by
  apply Subsingleton.elim

end YangMills.ClayCore
