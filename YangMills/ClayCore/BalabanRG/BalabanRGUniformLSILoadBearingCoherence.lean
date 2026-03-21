import Mathlib
import YangMills.ClayCore.BalabanRG.BalabanRGUniformLSILoadBearingPacket

namespace YangMills.ClayCore

/-- Dedicated coherence hub for the explicit load-bearing surface of the current
Balaban-RG / Haar-LSI lane. It centralizes constructors, projections, equivalences,
and round-trips for the load-bearing packet. -/
theorem balaban_rg_uniform_lsi_load_bearing_packet_of_live_target
    (d N_c : ℕ) [NeZero N_c]
    (tr : HaarLSIFromUniformLSITransfer N_c)
    (h : BalabanRGUniformLSILiveTarget d N_c) :
    BalabanRGUniformLSILoadBearingPacket d N_c := by
  exact
    balaban_rg_uniform_lsi_load_bearing_packet_of_activation_data d N_c
      (balaban_rg_uniform_lsi_activation_data_of_live_target d N_c tr h)

theorem balaban_rg_uniform_lsi_load_bearing_packet_of_direct_uniform_theorem_target
    (d N_c : ℕ) [NeZero N_c]
    (tr : HaarLSIFromUniformLSITransfer N_c)
    (h : SpecialUnitaryDirectUniformLSITheoremTarget d N_c) :
    BalabanRGUniformLSILoadBearingPacket d N_c := by
  exact
    balaban_rg_uniform_lsi_load_bearing_packet_of_activation_data d N_c
      (balaban_rg_uniform_lsi_activation_data_of_direct_uniform_theorem_target d N_c tr h)

theorem balaban_rg_uniform_lsi_load_bearing_packet_of_conditional_target
    (d N_c : ℕ) [NeZero N_c]
    (tr : HaarLSIFromUniformLSITransfer N_c)
    (h : BalabanRGUniformLSIConditionalTarget d N_c) :
    BalabanRGUniformLSILoadBearingPacket d N_c := by
  exact
    balaban_rg_uniform_lsi_load_bearing_packet_of_activation_data d N_c
      (balaban_rg_uniform_lsi_activation_data_of_conditional_target d N_c tr h)

theorem balaban_rg_uniform_lsi_load_bearing_packet_of_haar_lsi_live_target
    (d N_c : ℕ) [NeZero N_c]
    (tr : HaarLSIFromUniformLSITransfer N_c)
    (h : HaarLSILiveTarget d N_c) :
    BalabanRGUniformLSILoadBearingPacket d N_c := by
  exact
    balaban_rg_uniform_lsi_load_bearing_packet_of_activation_data d N_c
      (balaban_rg_uniform_lsi_activation_data_of_haar_lsi_live_target d N_c tr h)

theorem balaban_rg_uniform_lsi_load_bearing_packet_of_pkg
    (d N_c : ℕ) [NeZero N_c]
    (tr : HaarLSIFromUniformLSITransfer N_c)
    (pkg : BalabanRGPackage d N_c) :
    BalabanRGUniformLSILoadBearingPacket d N_c := by
  exact
    balaban_rg_uniform_lsi_load_bearing_packet_of_activation_data d N_c
      (balaban_rg_uniform_lsi_activation_data_of_pkg d N_c tr pkg)

theorem balaban_rg_uniform_lsi_load_bearing_packet_of_pkg_witness
    (d N_c : ℕ) [NeZero N_c]
    (tr : HaarLSIFromUniformLSITransfer N_c)
    (h : ∃ _ : BalabanRGPackage d N_c, True) :
    BalabanRGUniformLSILoadBearingPacket d N_c := by
  exact
    balaban_rg_uniform_lsi_load_bearing_packet_of_activation_data d N_c
      (balaban_rg_uniform_lsi_activation_data_of_pkg_witness d N_c tr h)

theorem public_facade_of_balaban_rg_uniform_lsi_load_bearing_packet
    {d N_c : ℕ} [NeZero N_c]
    (packet : BalabanRGUniformLSILoadBearingPacket d N_c) :
    BalabanRGUniformLSIPublicFacade d N_c := by
  exact
    balaban_rg_uniform_lsi_public_facade_of_activation_data d N_c
      (activation_data_of_balaban_rg_uniform_lsi_load_bearing_packet packet)

theorem lane_contract_of_balaban_rg_uniform_lsi_load_bearing_packet
    {d N_c : ℕ} [NeZero N_c]
    (packet : BalabanRGUniformLSILoadBearingPacket d N_c) :
    BalabanRGUniformLSILaneContract d N_c := by
  exact
    balaban_rg_uniform_lsi_lane_contract_of_activation_data d N_c
      (activation_data_of_balaban_rg_uniform_lsi_load_bearing_packet packet)

theorem closure_package_of_balaban_rg_uniform_lsi_load_bearing_packet
    {d N_c : ℕ} [NeZero N_c]
    (packet : BalabanRGUniformLSILoadBearingPacket d N_c) :
    BalabanRGUniformLSIClosurePackage d N_c := by
  exact
    balaban_rg_uniform_lsi_closure_package_of_activation_data d N_c
      (activation_data_of_balaban_rg_uniform_lsi_load_bearing_packet packet)

theorem equivalence_registry_of_balaban_rg_uniform_lsi_load_bearing_packet
    {d N_c : ℕ} [NeZero N_c]
    (packet : BalabanRGUniformLSILoadBearingPacket d N_c) :
    BalabanRGUniformLSIEquivalenceRegistry d N_c := by
  exact
    balaban_rg_uniform_lsi_equivalence_registry_of_activation_data d N_c
      (activation_data_of_balaban_rg_uniform_lsi_load_bearing_packet packet)

theorem last_mile_output_of_balaban_rg_uniform_lsi_load_bearing_packet
    {d N_c : ℕ} [NeZero N_c]
    (packet : BalabanRGUniformLSILoadBearingPacket d N_c) :
    BalabanRGUniformLSILastMileOutput d N_c := by
  exact
    balaban_rg_uniform_lsi_last_mile_output_of_activation_data d N_c
      (activation_data_of_balaban_rg_uniform_lsi_load_bearing_packet packet)

theorem direct_uniform_theorem_target_of_balaban_rg_uniform_lsi_load_bearing_packet
    {d N_c : ℕ} [NeZero N_c]
    (packet : BalabanRGUniformLSILoadBearingPacket d N_c) :
    SpecialUnitaryDirectUniformLSITheoremTarget d N_c := by
  exact
    direct_uniform_theorem_target_of_activation_data
      (activation_data_of_balaban_rg_uniform_lsi_load_bearing_packet packet)

theorem haar_lsi_live_target_of_balaban_rg_uniform_lsi_load_bearing_packet
    {d N_c : ℕ} [NeZero N_c]
    (packet : BalabanRGUniformLSILoadBearingPacket d N_c) :
    HaarLSILiveTarget d N_c := by
  exact
    haar_lsi_live_target_of_activation_data
      (activation_data_of_balaban_rg_uniform_lsi_load_bearing_packet packet)

theorem pkg_witness_of_balaban_rg_uniform_lsi_load_bearing_packet
    {d N_c : ℕ} [NeZero N_c]
    (packet : BalabanRGUniformLSILoadBearingPacket d N_c) :
    ∃ _ : BalabanRGPackage d N_c, True := by
  exact
    pkg_witness_of_activation_data
      (activation_data_of_balaban_rg_uniform_lsi_load_bearing_packet packet)

theorem balaban_rg_uniform_lsi_load_bearing_packet_iff_live_target
    (d N_c : ℕ) [NeZero N_c] :
    BalabanRGUniformLSILoadBearingPacket d N_c ↔
      (HaarLSIFromUniformLSITransfer N_c ∧ BalabanRGUniformLSILiveTarget d N_c) := by
  constructor
  · intro packet
    exact
      ⟨transfer_of_balaban_rg_uniform_lsi_load_bearing_packet packet,
        live_target_of_balaban_rg_uniform_lsi_load_bearing_packet packet⟩
  · intro h
    exact balaban_rg_uniform_lsi_load_bearing_packet_of_live_target d N_c h.1 h.2

theorem balaban_rg_uniform_lsi_load_bearing_packet_iff_direct_uniform_theorem_target
    (d N_c : ℕ) [NeZero N_c] :
    BalabanRGUniformLSILoadBearingPacket d N_c ↔
      (HaarLSIFromUniformLSITransfer N_c ∧
        SpecialUnitaryDirectUniformLSITheoremTarget d N_c) := by
  constructor
  · intro packet
    exact
      ⟨transfer_of_balaban_rg_uniform_lsi_load_bearing_packet packet,
        direct_uniform_theorem_target_of_balaban_rg_uniform_lsi_load_bearing_packet packet⟩
  · intro h
    exact
      balaban_rg_uniform_lsi_load_bearing_packet_of_direct_uniform_theorem_target
        d N_c h.1 h.2

theorem balaban_rg_uniform_lsi_load_bearing_packet_iff_conditional_target
    (d N_c : ℕ) [NeZero N_c] :
    BalabanRGUniformLSILoadBearingPacket d N_c ↔
      (HaarLSIFromUniformLSITransfer N_c ∧ BalabanRGUniformLSIConditionalTarget d N_c) := by
  constructor
  · intro packet
    exact
      ⟨transfer_of_balaban_rg_uniform_lsi_load_bearing_packet packet,
        conditional_target_of_balaban_rg_uniform_lsi_load_bearing_packet packet⟩
  · intro h
    exact balaban_rg_uniform_lsi_load_bearing_packet_of_conditional_target d N_c h.1 h.2

theorem balaban_rg_uniform_lsi_load_bearing_packet_iff_haar_lsi_live_target
    (d N_c : ℕ) [NeZero N_c] :
    BalabanRGUniformLSILoadBearingPacket d N_c ↔
      (HaarLSIFromUniformLSITransfer N_c ∧ HaarLSILiveTarget d N_c) := by
  constructor
  · intro packet
    exact
      ⟨transfer_of_balaban_rg_uniform_lsi_load_bearing_packet packet,
        haar_lsi_live_target_of_balaban_rg_uniform_lsi_load_bearing_packet packet⟩
  · intro h
    exact
      balaban_rg_uniform_lsi_load_bearing_packet_of_haar_lsi_live_target
        d N_c h.1 h.2

theorem balaban_rg_uniform_lsi_load_bearing_packet_iff_pkg_witness
    (d N_c : ℕ) [NeZero N_c] :
    BalabanRGUniformLSILoadBearingPacket d N_c ↔
      (HaarLSIFromUniformLSITransfer N_c ∧
        (∃ _ : BalabanRGPackage d N_c, True)) := by
  constructor
  · intro packet
    exact
      ⟨transfer_of_balaban_rg_uniform_lsi_load_bearing_packet packet,
        pkg_witness_of_balaban_rg_uniform_lsi_load_bearing_packet packet⟩
  · intro h
    exact balaban_rg_uniform_lsi_load_bearing_packet_of_pkg_witness d N_c h.1 h.2

theorem balaban_rg_uniform_lsi_activation_data_of_load_bearing_packet_of_activation_data_eq_canonical
    {d N_c : ℕ} [NeZero N_c]
    (data : BalabanRGUniformLSIActivationData d N_c) :
    activation_data_of_balaban_rg_uniform_lsi_load_bearing_packet
      (balaban_rg_uniform_lsi_load_bearing_packet_of_activation_data d N_c data) = data := by
  rfl

theorem balaban_rg_uniform_lsi_direct_input_of_load_bearing_packet_of_direct_input_eq_canonical
    {d N_c : ℕ} [NeZero N_c]
    (input : BalabanRGUniformLSIDirectInput d N_c) :
    direct_input_of_balaban_rg_uniform_lsi_load_bearing_packet
      (balaban_rg_uniform_lsi_load_bearing_packet_of_direct_input d N_c input) = input := by
  apply Subsingleton.elim

theorem balaban_rg_uniform_lsi_concrete_input_of_load_bearing_packet_of_concrete_input_eq_canonical
    {d N_c : ℕ} [NeZero N_c]
    (input : BalabanRGUniformLSIConcreteInput d N_c) :
    concrete_input_of_balaban_rg_uniform_lsi_load_bearing_packet
      (balaban_rg_uniform_lsi_load_bearing_packet_of_concrete_input d N_c input) = input := by
  apply Subsingleton.elim

theorem balaban_rg_uniform_lsi_end_to_end_packet_of_load_bearing_packet_of_end_to_end_packet_eq_canonical
    {d N_c : ℕ} [NeZero N_c]
    (packet : BalabanRGUniformLSIEndToEndPacket d N_c) :
    end_to_end_packet_of_balaban_rg_uniform_lsi_load_bearing_packet
      (balaban_rg_uniform_lsi_load_bearing_packet_of_end_to_end_packet packet) = packet := by
  apply Subsingleton.elim

theorem balaban_rg_uniform_lsi_public_facade_eq_canonical_of_load_bearing_packet
    {d N_c : ℕ} [NeZero N_c]
    (packet : BalabanRGUniformLSILoadBearingPacket d N_c) :
    public_facade_of_balaban_rg_uniform_lsi_load_bearing_packet packet =
      balaban_rg_uniform_lsi_public_facade_of_activation_data d N_c
        (activation_data_of_balaban_rg_uniform_lsi_load_bearing_packet packet) := by
  rfl

theorem balaban_rg_uniform_lsi_lane_contract_eq_canonical_of_load_bearing_packet
    {d N_c : ℕ} [NeZero N_c]
    (packet : BalabanRGUniformLSILoadBearingPacket d N_c) :
    lane_contract_of_balaban_rg_uniform_lsi_load_bearing_packet packet =
      balaban_rg_uniform_lsi_lane_contract_of_activation_data d N_c
        (activation_data_of_balaban_rg_uniform_lsi_load_bearing_packet packet) := by
  rfl

end YangMills.ClayCore
