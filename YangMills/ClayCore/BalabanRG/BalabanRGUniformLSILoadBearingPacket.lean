import Mathlib
import YangMills.ClayCore.BalabanRG.BalabanRGUniformLSIPillarIIPacket

namespace YangMills.ClayCore

/-- Explicit packet isolating the current load-bearing Pillar II surfaces of the
Balaban-RG / Haar-LSI lane. -/
structure BalabanRGUniformLSILoadBearingPacket (d N_c : ℕ) [NeZero N_c] : Prop where
  activation : BalabanRGUniformLSIActivationData d N_c
  frontier : BalabanRGUniformLSIFrontier d N_c
  liveTarget : BalabanRGUniformLSILiveTarget d N_c
  conditionalTarget : BalabanRGUniformLSIConditionalTarget d N_c
  scaleTarget : SpecialUnitaryScaleLSITarget d N_c
  haarTarget : HaarLSITarget N_c
  frontierPackage : HaarLSIFrontierPackage d N_c

/-- Canonical load-bearing packet from the abstract activation packet. -/
theorem balaban_rg_uniform_lsi_load_bearing_packet_of_activation_data
    (d N_c : ℕ) [NeZero N_c]
    (data : BalabanRGUniformLSIActivationData d N_c) :
    BalabanRGUniformLSILoadBearingPacket d N_c := by
  let frontier : BalabanRGUniformLSIFrontier d N_c :=
    balaban_rg_uniform_lsi_frontier_of_activation_data d N_c data
  exact
    { activation := data
      frontier := frontier
      liveTarget := data.liveTarget
      conditionalTarget := conditional_target_of_activation_data data
      scaleTarget := scale_target_of_activation_data data
      haarTarget := haar_target_of_activation_data data
      frontierPackage := frontier_package_of_activation_data data }

/-- Canonical load-bearing packet from the short public frontier. -/
theorem balaban_rg_uniform_lsi_load_bearing_packet_of_frontier
    {d N_c : ℕ} [NeZero N_c]
    (frontier : BalabanRGUniformLSIFrontier d N_c) :
    BalabanRGUniformLSILoadBearingPacket d N_c := by
  exact
    balaban_rg_uniform_lsi_load_bearing_packet_of_activation_data d N_c
      (activation_data_of_balaban_rg_uniform_lsi_frontier frontier)

/-- Canonical load-bearing packet from the direct input packet. -/
theorem balaban_rg_uniform_lsi_load_bearing_packet_of_direct_input
    (d N_c : ℕ) [NeZero N_c]
    (input : BalabanRGUniformLSIDirectInput d N_c) :
    BalabanRGUniformLSILoadBearingPacket d N_c := by
  exact
    balaban_rg_uniform_lsi_load_bearing_packet_of_activation_data d N_c
      (activation_data_of_balaban_rg_uniform_lsi_direct_input d N_c input)

/-- Canonical load-bearing packet from the concrete input packet. -/
theorem balaban_rg_uniform_lsi_load_bearing_packet_of_concrete_input
    (d N_c : ℕ) [NeZero N_c]
    (input : BalabanRGUniformLSIConcreteInput d N_c) :
    BalabanRGUniformLSILoadBearingPacket d N_c := by
  exact
    balaban_rg_uniform_lsi_load_bearing_packet_of_activation_data d N_c
      (balaban_rg_uniform_lsi_activation_data_of_concrete_input d N_c input)

/-- Canonical load-bearing packet from the obstruction packet. -/
theorem balaban_rg_uniform_lsi_load_bearing_packet_of_obstruction_packet
    {d N_c : ℕ} [NeZero N_c]
    (packet : BalabanRGUniformLSIObstructionPacket d N_c) :
    BalabanRGUniformLSILoadBearingPacket d N_c := by
  exact
    balaban_rg_uniform_lsi_load_bearing_packet_of_activation_data d N_c
      (activation_data_of_balaban_rg_uniform_lsi_obstruction_packet packet)

/-- Canonical load-bearing packet from the unified end-to-end packet. -/
theorem balaban_rg_uniform_lsi_load_bearing_packet_of_end_to_end_packet
    {d N_c : ℕ} [NeZero N_c]
    (packet : BalabanRGUniformLSIEndToEndPacket d N_c) :
    BalabanRGUniformLSILoadBearingPacket d N_c := by
  exact
    balaban_rg_uniform_lsi_load_bearing_packet_of_activation_data d N_c
      (activation_data_of_balaban_rg_uniform_lsi_end_to_end_packet packet)

/-- Canonical load-bearing packet from the Pillar II packet. -/
theorem balaban_rg_uniform_lsi_load_bearing_packet_of_pillar_ii_packet
    {d N_c : ℕ} [NeZero N_c]
    (packet : BalabanRGUniformLSIPillarIIPacket d N_c) :
    BalabanRGUniformLSILoadBearingPacket d N_c := by
  exact
    balaban_rg_uniform_lsi_load_bearing_packet_of_activation_data d N_c
      (activation_data_of_balaban_rg_uniform_lsi_pillar_ii_packet packet)

/-- Projection to the abstract activation packet. -/
theorem activation_data_of_balaban_rg_uniform_lsi_load_bearing_packet
    {d N_c : ℕ} [NeZero N_c]
    (packet : BalabanRGUniformLSILoadBearingPacket d N_c) :
    BalabanRGUniformLSIActivationData d N_c := by
  exact packet.activation

/-- Projection to the short public frontier. -/
theorem frontier_of_balaban_rg_uniform_lsi_load_bearing_packet
    {d N_c : ℕ} [NeZero N_c]
    (packet : BalabanRGUniformLSILoadBearingPacket d N_c) :
    BalabanRGUniformLSIFrontier d N_c := by
  exact packet.frontier

/-- Projection to the preferred live target. -/
theorem live_target_of_balaban_rg_uniform_lsi_load_bearing_packet
    {d N_c : ℕ} [NeZero N_c]
    (packet : BalabanRGUniformLSILoadBearingPacket d N_c) :
    BalabanRGUniformLSILiveTarget d N_c := by
  exact packet.liveTarget

/-- Projection to the old conditional target name. -/
theorem conditional_target_of_balaban_rg_uniform_lsi_load_bearing_packet
    {d N_c : ℕ} [NeZero N_c]
    (packet : BalabanRGUniformLSILoadBearingPacket d N_c) :
    BalabanRGUniformLSIConditionalTarget d N_c := by
  exact packet.conditionalTarget

/-- Projection to the scale target. -/
theorem scale_target_of_balaban_rg_uniform_lsi_load_bearing_packet
    {d N_c : ℕ} [NeZero N_c]
    (packet : BalabanRGUniformLSILoadBearingPacket d N_c) :
    SpecialUnitaryScaleLSITarget d N_c := by
  exact packet.scaleTarget

/-- Projection to the Haar target. -/
theorem haar_target_of_balaban_rg_uniform_lsi_load_bearing_packet
    {d N_c : ℕ} [NeZero N_c]
    (packet : BalabanRGUniformLSILoadBearingPacket d N_c) :
    HaarLSITarget N_c := by
  exact packet.haarTarget

/-- Projection to the frontier package. -/
theorem frontier_package_of_balaban_rg_uniform_lsi_load_bearing_packet
    {d N_c : ℕ} [NeZero N_c]
    (packet : BalabanRGUniformLSILoadBearingPacket d N_c) :
    HaarLSIFrontierPackage d N_c := by
  exact packet.frontierPackage

/-- Projection to the transfer ingredient. -/
theorem transfer_of_balaban_rg_uniform_lsi_load_bearing_packet
    {d N_c : ℕ} [NeZero N_c]
    (packet : BalabanRGUniformLSILoadBearingPacket d N_c) :
    HaarLSIFromUniformLSITransfer N_c := by
  exact packet.activation.transfer

/-- Projection to the direct input packet. -/
theorem direct_input_of_balaban_rg_uniform_lsi_load_bearing_packet
    {d N_c : ℕ} [NeZero N_c]
    (packet : BalabanRGUniformLSILoadBearingPacket d N_c) :
    BalabanRGUniformLSIDirectInput d N_c := by
  exact
    balaban_rg_uniform_lsi_direct_input_of_activation_data
      (activation_data_of_balaban_rg_uniform_lsi_load_bearing_packet packet)

/-- Projection to the concrete input packet. -/
theorem concrete_input_of_balaban_rg_uniform_lsi_load_bearing_packet
    {d N_c : ℕ} [NeZero N_c]
    (packet : BalabanRGUniformLSILoadBearingPacket d N_c) :
    BalabanRGUniformLSIConcreteInput d N_c := by
  exact
    balaban_rg_uniform_lsi_concrete_input_of_activation_data
      (activation_data_of_balaban_rg_uniform_lsi_load_bearing_packet packet)

/-- Projection to the obstruction packet. -/
theorem obstruction_packet_of_balaban_rg_uniform_lsi_load_bearing_packet
    {d N_c : ℕ} [NeZero N_c]
    (packet : BalabanRGUniformLSILoadBearingPacket d N_c) :
    BalabanRGUniformLSIObstructionPacket d N_c := by
  exact
    balaban_rg_uniform_lsi_obstruction_packet_of_activation_data d N_c
      (activation_data_of_balaban_rg_uniform_lsi_load_bearing_packet packet)

/-- Projection to the unified end-to-end packet. -/
theorem end_to_end_packet_of_balaban_rg_uniform_lsi_load_bearing_packet
    {d N_c : ℕ} [NeZero N_c]
    (packet : BalabanRGUniformLSILoadBearingPacket d N_c) :
    BalabanRGUniformLSIEndToEndPacket d N_c := by
  exact
    balaban_rg_uniform_lsi_end_to_end_packet_of_activation_data d N_c
      (activation_data_of_balaban_rg_uniform_lsi_load_bearing_packet packet)

/-- Projection to the Pillar II packet. -/
theorem pillar_ii_packet_of_balaban_rg_uniform_lsi_load_bearing_packet
    {d N_c : ℕ} [NeZero N_c]
    (packet : BalabanRGUniformLSILoadBearingPacket d N_c) :
    BalabanRGUniformLSIPillarIIPacket d N_c := by
  exact
    balaban_rg_uniform_lsi_pillar_ii_packet_of_activation_data d N_c
      (activation_data_of_balaban_rg_uniform_lsi_load_bearing_packet packet)

/-- Logical normal form: the load-bearing packet is equivalent to the abstract activation packet. -/
theorem balaban_rg_uniform_lsi_load_bearing_packet_iff_activation_data
    (d N_c : ℕ) [NeZero N_c] :
    BalabanRGUniformLSILoadBearingPacket d N_c ↔
      BalabanRGUniformLSIActivationData d N_c := by
  constructor
  · intro packet
    exact packet.activation
  · intro data
    exact balaban_rg_uniform_lsi_load_bearing_packet_of_activation_data d N_c data

/-- Logical normal form: the load-bearing packet is equivalent to the short public frontier. -/
theorem balaban_rg_uniform_lsi_load_bearing_packet_iff_frontier
    (d N_c : ℕ) [NeZero N_c] :
    BalabanRGUniformLSILoadBearingPacket d N_c ↔
      BalabanRGUniformLSIFrontier d N_c := by
  constructor
  · intro packet
    exact packet.frontier
  · intro frontier
    exact balaban_rg_uniform_lsi_load_bearing_packet_of_frontier frontier

/-- Logical normal form: the load-bearing packet is equivalent to the direct input packet. -/
theorem balaban_rg_uniform_lsi_load_bearing_packet_iff_direct_input
    (d N_c : ℕ) [NeZero N_c] :
    BalabanRGUniformLSILoadBearingPacket d N_c ↔
      BalabanRGUniformLSIDirectInput d N_c := by
  constructor
  · intro packet
    exact direct_input_of_balaban_rg_uniform_lsi_load_bearing_packet packet
  · intro input
    exact balaban_rg_uniform_lsi_load_bearing_packet_of_direct_input d N_c input

/-- Logical normal form: the load-bearing packet is equivalent to the concrete input packet. -/
theorem balaban_rg_uniform_lsi_load_bearing_packet_iff_concrete_input
    (d N_c : ℕ) [NeZero N_c] :
    BalabanRGUniformLSILoadBearingPacket d N_c ↔
      BalabanRGUniformLSIConcreteInput d N_c := by
  constructor
  · intro packet
    exact concrete_input_of_balaban_rg_uniform_lsi_load_bearing_packet packet
  · intro input
    exact balaban_rg_uniform_lsi_load_bearing_packet_of_concrete_input d N_c input

/-- Logical normal form: the load-bearing packet is equivalent to the obstruction packet. -/
theorem balaban_rg_uniform_lsi_load_bearing_packet_iff_obstruction_packet
    (d N_c : ℕ) [NeZero N_c] :
    BalabanRGUniformLSILoadBearingPacket d N_c ↔
      BalabanRGUniformLSIObstructionPacket d N_c := by
  constructor
  · intro packet
    exact obstruction_packet_of_balaban_rg_uniform_lsi_load_bearing_packet packet
  · intro obstruction
    exact balaban_rg_uniform_lsi_load_bearing_packet_of_obstruction_packet obstruction

/-- Logical normal form: the load-bearing packet is equivalent to the unified end-to-end packet. -/
theorem balaban_rg_uniform_lsi_load_bearing_packet_iff_end_to_end_packet
    (d N_c : ℕ) [NeZero N_c] :
    BalabanRGUniformLSILoadBearingPacket d N_c ↔
      BalabanRGUniformLSIEndToEndPacket d N_c := by
  constructor
  · intro packet
    exact end_to_end_packet_of_balaban_rg_uniform_lsi_load_bearing_packet packet
  · intro e2e
    exact balaban_rg_uniform_lsi_load_bearing_packet_of_end_to_end_packet e2e

/-- Logical normal form: the load-bearing packet is equivalent to the Pillar II packet. -/
theorem balaban_rg_uniform_lsi_load_bearing_packet_iff_pillar_ii_packet
    (d N_c : ℕ) [NeZero N_c] :
    BalabanRGUniformLSILoadBearingPacket d N_c ↔
      BalabanRGUniformLSIPillarIIPacket d N_c := by
  constructor
  · intro packet
    exact pillar_ii_packet_of_balaban_rg_uniform_lsi_load_bearing_packet packet
  · intro p2
    exact balaban_rg_uniform_lsi_load_bearing_packet_of_pillar_ii_packet p2

/-- Coherence: the load-bearing packet is propositionally equal to the canonical one reconstructed from its activation data. -/
theorem balaban_rg_uniform_lsi_load_bearing_packet_eq_canonical_of_activation_data
    {d N_c : ℕ} [NeZero N_c]
    (packet : BalabanRGUniformLSILoadBearingPacket d N_c) :
    packet =
      balaban_rg_uniform_lsi_load_bearing_packet_of_activation_data d N_c
        (activation_data_of_balaban_rg_uniform_lsi_load_bearing_packet packet) := by
  apply Subsingleton.elim

/-- Round-trip coherence: frontier → load-bearing → frontier is canonically the identity. -/
theorem balaban_rg_uniform_lsi_frontier_of_load_bearing_packet_of_frontier_eq_canonical
    {d N_c : ℕ} [NeZero N_c]
    (frontier : BalabanRGUniformLSIFrontier d N_c) :
    frontier_of_balaban_rg_uniform_lsi_load_bearing_packet
      (balaban_rg_uniform_lsi_load_bearing_packet_of_frontier frontier) = frontier := by
  apply Subsingleton.elim

/-- Round-trip coherence: obstruction → load-bearing → obstruction is canonically the identity. -/
theorem balaban_rg_uniform_lsi_obstruction_packet_of_load_bearing_packet_of_obstruction_packet_eq_canonical
    {d N_c : ℕ} [NeZero N_c]
    (packet : BalabanRGUniformLSIObstructionPacket d N_c) :
    obstruction_packet_of_balaban_rg_uniform_lsi_load_bearing_packet
      (balaban_rg_uniform_lsi_load_bearing_packet_of_obstruction_packet packet) = packet := by
  apply Subsingleton.elim

/-- Round-trip coherence: Pillar II → load-bearing → Pillar II is canonically the identity. -/
theorem balaban_rg_uniform_lsi_pillar_ii_packet_of_load_bearing_packet_of_pillar_ii_packet_eq_canonical
    {d N_c : ℕ} [NeZero N_c]
    (packet : BalabanRGUniformLSIPillarIIPacket d N_c) :
    pillar_ii_packet_of_balaban_rg_uniform_lsi_load_bearing_packet
      (balaban_rg_uniform_lsi_load_bearing_packet_of_pillar_ii_packet packet) = packet := by
  apply Subsingleton.elim

end YangMills.ClayCore
