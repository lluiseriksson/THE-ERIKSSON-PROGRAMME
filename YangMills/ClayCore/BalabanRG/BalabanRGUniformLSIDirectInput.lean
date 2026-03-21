import Mathlib
import YangMills.ClayCore.BalabanRG.BalabanRGUniformLSIConcreteInput

namespace YangMills.ClayCore

/-- Explicit public input packet for the direct uniform-theorem surface of the
current Balaban-RG / Haar-LSI lane. -/
structure BalabanRGUniformLSIDirectInput (d N_c : ℕ) [NeZero N_c] : Prop where
  transfer : HaarLSIFromUniformLSITransfer N_c
  directTarget : SpecialUnitaryDirectUniformLSITheoremTarget d N_c

/-- Direct input packet from the direct uniform-theorem target itself. -/
theorem balaban_rg_uniform_lsi_direct_input_of_direct_uniform_theorem_target
    (d N_c : ℕ) [NeZero N_c]
    (tr : HaarLSIFromUniformLSITransfer N_c)
    (h : SpecialUnitaryDirectUniformLSITheoremTarget d N_c) :
    BalabanRGUniformLSIDirectInput d N_c := by
  exact ⟨tr, h⟩

/-- Direct input packet from an actual Balaban-RG package witness. -/
theorem balaban_rg_uniform_lsi_direct_input_of_pkg
    (d N_c : ℕ) [NeZero N_c]
    (tr : HaarLSIFromUniformLSITransfer N_c)
    (pkg : BalabanRGPackage d N_c) :
    BalabanRGUniformLSIDirectInput d N_c := by
  exact ⟨tr, direct_uniform_theorem_target_of_pkg pkg⟩

/-- Direct input packet from the bare package-witness form. -/
theorem balaban_rg_uniform_lsi_direct_input_of_pkg_witness
    (d N_c : ℕ) [NeZero N_c]
    (tr : HaarLSIFromUniformLSITransfer N_c)
    (h : ∃ _ : BalabanRGPackage d N_c, True) :
    BalabanRGUniformLSIDirectInput d N_c := by
  rcases h with ⟨pkg, _⟩
  exact ⟨tr, direct_uniform_theorem_target_of_pkg pkg⟩

/-- Direct input packet recovered from the abstract activation packet. -/
theorem balaban_rg_uniform_lsi_direct_input_of_activation_data
    {d N_c : ℕ} [NeZero N_c]
    (data : BalabanRGUniformLSIActivationData d N_c) :
    BalabanRGUniformLSIDirectInput d N_c := by
  exact ⟨data.transfer, direct_uniform_theorem_target_of_activation_data data⟩

/-- Direct input packet recovered from the concrete package-witness packet. -/
theorem balaban_rg_uniform_lsi_direct_input_of_concrete_input
    {d N_c : ℕ} [NeZero N_c]
    (input : BalabanRGUniformLSIConcreteInput d N_c) :
    BalabanRGUniformLSIDirectInput d N_c := by
  exact
    balaban_rg_uniform_lsi_direct_input_of_activation_data
      (balaban_rg_uniform_lsi_activation_data_of_concrete_input d N_c input)

/-- Abstract activation packet recovered from the direct input packet. -/
theorem activation_data_of_balaban_rg_uniform_lsi_direct_input
    (d N_c : ℕ) [NeZero N_c]
    (input : BalabanRGUniformLSIDirectInput d N_c) :
    BalabanRGUniformLSIActivationData d N_c := by
  exact
    balaban_rg_uniform_lsi_activation_data_of_direct_uniform_theorem_target d N_c
      input.transfer input.directTarget

/-- Concrete package-witness packet recovered from the direct input packet. -/
theorem balaban_rg_uniform_lsi_concrete_input_of_direct_input
    (d N_c : ℕ) [NeZero N_c]
    (input : BalabanRGUniformLSIDirectInput d N_c) :
    BalabanRGUniformLSIConcreteInput d N_c := by
  exact
    balaban_rg_uniform_lsi_concrete_input_of_activation_data
      (activation_data_of_balaban_rg_uniform_lsi_direct_input d N_c input)

/-- Short public frontier recovered from the direct input packet. -/
theorem balaban_rg_uniform_lsi_frontier_of_direct_input
    (d N_c : ℕ) [NeZero N_c]
    (input : BalabanRGUniformLSIDirectInput d N_c) :
    BalabanRGUniformLSIFrontier d N_c := by
  exact
    balaban_rg_uniform_lsi_frontier_of_activation_data d N_c
      (activation_data_of_balaban_rg_uniform_lsi_direct_input d N_c input)

/-- Canonical lane contract recovered from the direct input packet. -/
theorem balaban_rg_uniform_lsi_lane_contract_of_direct_input
    (d N_c : ℕ) [NeZero N_c]
    (input : BalabanRGUniformLSIDirectInput d N_c) :
    BalabanRGUniformLSILaneContract d N_c := by
  exact
    balaban_rg_uniform_lsi_lane_contract_of_activation_data d N_c
      (activation_data_of_balaban_rg_uniform_lsi_direct_input d N_c input)

/-- Public facade recovered from the direct input packet. -/
theorem balaban_rg_uniform_lsi_public_facade_of_direct_input
    (d N_c : ℕ) [NeZero N_c]
    (input : BalabanRGUniformLSIDirectInput d N_c) :
    BalabanRGUniformLSIPublicFacade d N_c := by
  exact
    balaban_rg_uniform_lsi_public_facade_of_activation_data d N_c
      (activation_data_of_balaban_rg_uniform_lsi_direct_input d N_c input)

/-- Logical normal form: the direct input packet is equivalent to the abstract activation packet. -/
theorem balaban_rg_uniform_lsi_direct_input_iff_activation_data
    (d N_c : ℕ) [NeZero N_c] :
    BalabanRGUniformLSIDirectInput d N_c ↔
      BalabanRGUniformLSIActivationData d N_c := by
  constructor
  · intro input
    exact activation_data_of_balaban_rg_uniform_lsi_direct_input d N_c input
  · intro data
    exact balaban_rg_uniform_lsi_direct_input_of_activation_data data

/-- Logical normal form: the direct input packet is equivalent to the short public frontier. -/
theorem balaban_rg_uniform_lsi_direct_input_iff_frontier
    (d N_c : ℕ) [NeZero N_c] :
    BalabanRGUniformLSIDirectInput d N_c ↔
      BalabanRGUniformLSIFrontier d N_c := by
  constructor
  · intro input
    exact balaban_rg_uniform_lsi_frontier_of_direct_input d N_c input
  · intro frontier
    exact
      balaban_rg_uniform_lsi_direct_input_of_activation_data
        (activation_data_of_balaban_rg_uniform_lsi_frontier frontier)

/-- Logical normal form: the direct input packet is equivalent to the concrete package-witness packet. -/
theorem balaban_rg_uniform_lsi_direct_input_iff_concrete_input
    (d N_c : ℕ) [NeZero N_c] :
    BalabanRGUniformLSIDirectInput d N_c ↔
      BalabanRGUniformLSIConcreteInput d N_c := by
  constructor
  · intro input
    exact balaban_rg_uniform_lsi_concrete_input_of_direct_input d N_c input
  · intro input
    exact balaban_rg_uniform_lsi_direct_input_of_concrete_input input

/-- Coherence: the direct input packet is propositionally equal to the canonical one reconstructed from its activation data. -/
theorem balaban_rg_uniform_lsi_direct_input_eq_canonical_of_activation_data
    {d N_c : ℕ} [NeZero N_c]
    (input : BalabanRGUniformLSIDirectInput d N_c) :
    input =
      balaban_rg_uniform_lsi_direct_input_of_activation_data
        (activation_data_of_balaban_rg_uniform_lsi_direct_input d N_c input) := by
  apply Subsingleton.elim

/-- Projection to the transfer ingredient. -/
theorem transfer_of_balaban_rg_uniform_lsi_direct_input
    {d N_c : ℕ} [NeZero N_c]
    (input : BalabanRGUniformLSIDirectInput d N_c) :
    HaarLSIFromUniformLSITransfer N_c := by
  exact input.transfer

/-- Projection to the direct uniform-theorem target. -/
theorem direct_uniform_theorem_target_of_balaban_rg_uniform_lsi_direct_input
    {d N_c : ℕ} [NeZero N_c]
    (input : BalabanRGUniformLSIDirectInput d N_c) :
    SpecialUnitaryDirectUniformLSITheoremTarget d N_c := by
  exact input.directTarget

/-- Projection to the preferred live target. -/
theorem live_target_of_balaban_rg_uniform_lsi_direct_input
    {d N_c : ℕ} [NeZero N_c]
    (input : BalabanRGUniformLSIDirectInput d N_c) :
    BalabanRGUniformLSILiveTarget d N_c := by
  exact
    live_target_of_balaban_rg_uniform_lsi_activation_data
      (activation_data_of_balaban_rg_uniform_lsi_direct_input d N_c input)

/-- Projection to the bare package-witness form. -/
theorem pkg_witness_of_balaban_rg_uniform_lsi_direct_input
    {d N_c : ℕ} [NeZero N_c]
    (input : BalabanRGUniformLSIDirectInput d N_c) :
    ∃ _ : BalabanRGPackage d N_c, True := by
  exact
    pkg_witness_of_activation_data
      (activation_data_of_balaban_rg_uniform_lsi_direct_input d N_c input)

/-- Projection to the scale target. -/
theorem scale_target_of_balaban_rg_uniform_lsi_direct_input
    {d N_c : ℕ} [NeZero N_c]
    (input : BalabanRGUniformLSIDirectInput d N_c) :
    SpecialUnitaryScaleLSITarget d N_c := by
  exact
    scale_target_of_balaban_rg_uniform_lsi_frontier
      (balaban_rg_uniform_lsi_frontier_of_direct_input d N_c input)

/-- Projection to the Haar target. -/
theorem haar_target_of_balaban_rg_uniform_lsi_direct_input
    {d N_c : ℕ} [NeZero N_c]
    (input : BalabanRGUniformLSIDirectInput d N_c) :
    HaarLSITarget N_c := by
  exact
    haar_target_of_balaban_rg_uniform_lsi_frontier
      (balaban_rg_uniform_lsi_frontier_of_direct_input d N_c input)

/-- Projection to the frontier package. -/
theorem frontier_package_of_balaban_rg_uniform_lsi_direct_input
    {d N_c : ℕ} [NeZero N_c]
    (input : BalabanRGUniformLSIDirectInput d N_c) :
    HaarLSIFrontierPackage d N_c := by
  exact
    frontier_package_of_balaban_rg_uniform_lsi_frontier
      (balaban_rg_uniform_lsi_frontier_of_direct_input d N_c input)

end YangMills.ClayCore
