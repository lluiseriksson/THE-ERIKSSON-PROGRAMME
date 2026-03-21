import Mathlib
import YangMills.ClayCore.BalabanRG.BalabanRGUniformLSIFrontier

namespace YangMills.ClayCore

/-- Most concrete public input packet for the current Balaban-RG / Haar-LSI lane:
it packages the transfer ingredient together with a bare `BalabanRGPackage` witness. -/
structure BalabanRGUniformLSIConcreteInput (d N_c : ℕ) [NeZero N_c] : Prop where
  transfer : HaarLSIFromUniformLSITransfer N_c
  pkgWitness : ∃ _ : BalabanRGPackage d N_c, True

/-- Concrete input packet from an actual Balaban-RG package witness. -/
theorem balaban_rg_uniform_lsi_concrete_input_of_pkg
    (d N_c : ℕ) [NeZero N_c]
    (tr : HaarLSIFromUniformLSITransfer N_c)
    (pkg : BalabanRGPackage d N_c) :
    BalabanRGUniformLSIConcreteInput d N_c := by
  exact ⟨tr, ⟨pkg, trivial⟩⟩

/-- Concrete input packet from the bare package-witness form. -/
theorem balaban_rg_uniform_lsi_concrete_input_of_pkg_witness
    (d N_c : ℕ) [NeZero N_c]
    (tr : HaarLSIFromUniformLSITransfer N_c)
    (h : ∃ _ : BalabanRGPackage d N_c, True) :
    BalabanRGUniformLSIConcreteInput d N_c := by
  exact ⟨tr, h⟩

/-- Concrete input packet recovered from the abstract activation packet. -/
theorem balaban_rg_uniform_lsi_concrete_input_of_activation_data
    {d N_c : ℕ} [NeZero N_c]
    (data : BalabanRGUniformLSIActivationData d N_c) :
    BalabanRGUniformLSIConcreteInput d N_c := by
  exact ⟨data.transfer, pkg_witness_of_activation_data data⟩

/-- Abstract activation packet recovered from the concrete input packet. -/
theorem balaban_rg_uniform_lsi_activation_data_of_concrete_input
    (d N_c : ℕ) [NeZero N_c]
    (input : BalabanRGUniformLSIConcreteInput d N_c) :
    BalabanRGUniformLSIActivationData d N_c := by
  exact
    balaban_rg_uniform_lsi_activation_data_of_pkg_witness d N_c
      input.transfer input.pkgWitness

/-- Short public frontier recovered from the concrete input packet. -/
theorem balaban_rg_uniform_lsi_frontier_of_concrete_input
    (d N_c : ℕ) [NeZero N_c]
    (input : BalabanRGUniformLSIConcreteInput d N_c) :
    BalabanRGUniformLSIFrontier d N_c := by
  exact
    balaban_rg_uniform_lsi_frontier_of_pkg_witness d N_c
      input.transfer input.pkgWitness

/-- Canonical lane contract recovered from the concrete input packet. -/
theorem balaban_rg_uniform_lsi_lane_contract_of_concrete_input
    (d N_c : ℕ) [NeZero N_c]
    (input : BalabanRGUniformLSIConcreteInput d N_c) :
    BalabanRGUniformLSILaneContract d N_c := by
  exact
    balaban_rg_uniform_lsi_lane_contract_of_activation_data d N_c
      (balaban_rg_uniform_lsi_activation_data_of_concrete_input d N_c input)

/-- Public facade recovered from the concrete input packet. -/
theorem balaban_rg_uniform_lsi_public_facade_of_concrete_input
    (d N_c : ℕ) [NeZero N_c]
    (input : BalabanRGUniformLSIConcreteInput d N_c) :
    BalabanRGUniformLSIPublicFacade d N_c := by
  exact
    public_facade_of_balaban_rg_uniform_lsi_frontier
      (balaban_rg_uniform_lsi_frontier_of_concrete_input d N_c input)

/-- Logical normal form: the concrete input packet is equivalent to the abstract activation packet. -/
theorem balaban_rg_uniform_lsi_concrete_input_iff_activation_data
    (d N_c : ℕ) [NeZero N_c] :
    BalabanRGUniformLSIConcreteInput d N_c ↔
      BalabanRGUniformLSIActivationData d N_c := by
  constructor
  · intro input
    exact balaban_rg_uniform_lsi_activation_data_of_concrete_input d N_c input
  · intro data
    exact balaban_rg_uniform_lsi_concrete_input_of_activation_data data

/-- Logical normal form: the concrete input packet is equivalent to the short public frontier. -/
theorem balaban_rg_uniform_lsi_concrete_input_iff_frontier
    (d N_c : ℕ) [NeZero N_c] :
    BalabanRGUniformLSIConcreteInput d N_c ↔
      BalabanRGUniformLSIFrontier d N_c := by
  constructor
  · intro input
    exact balaban_rg_uniform_lsi_frontier_of_concrete_input d N_c input
  · intro frontier
    exact
      balaban_rg_uniform_lsi_concrete_input_of_activation_data
        (activation_data_of_balaban_rg_uniform_lsi_frontier frontier)

/-- Coherence: the concrete input packet is propositionally equal to the canonical one reconstructed from its abstract activation packet. -/
theorem balaban_rg_uniform_lsi_concrete_input_eq_canonical_of_activation_data
    {d N_c : ℕ} [NeZero N_c]
    (input : BalabanRGUniformLSIConcreteInput d N_c) :
    input =
      balaban_rg_uniform_lsi_concrete_input_of_activation_data
        (balaban_rg_uniform_lsi_activation_data_of_concrete_input d N_c input) := by
  apply Subsingleton.elim

/-- Projection to the transfer ingredient. -/
theorem transfer_of_balaban_rg_uniform_lsi_concrete_input
    {d N_c : ℕ} [NeZero N_c]
    (input : BalabanRGUniformLSIConcreteInput d N_c) :
    HaarLSIFromUniformLSITransfer N_c := by
  exact input.transfer

/-- Projection to the bare package-witness form. -/
theorem pkg_witness_of_balaban_rg_uniform_lsi_concrete_input
    {d N_c : ℕ} [NeZero N_c]
    (input : BalabanRGUniformLSIConcreteInput d N_c) :
    ∃ _ : BalabanRGPackage d N_c, True := by
  exact input.pkgWitness

/-- Projection to the preferred live target. -/
theorem live_target_of_balaban_rg_uniform_lsi_concrete_input
    {d N_c : ℕ} [NeZero N_c]
    (input : BalabanRGUniformLSIConcreteInput d N_c) :
    BalabanRGUniformLSILiveTarget d N_c := by
  exact
    live_target_of_balaban_rg_uniform_lsi_activation_data
      (balaban_rg_uniform_lsi_activation_data_of_concrete_input d N_c input)

/-- Projection to the scale target. -/
theorem scale_target_of_balaban_rg_uniform_lsi_concrete_input
    {d N_c : ℕ} [NeZero N_c]
    (input : BalabanRGUniformLSIConcreteInput d N_c) :
    SpecialUnitaryScaleLSITarget d N_c := by
  exact
    scale_target_of_balaban_rg_uniform_lsi_frontier
      (balaban_rg_uniform_lsi_frontier_of_concrete_input d N_c input)

/-- Projection to the Haar target. -/
theorem haar_target_of_balaban_rg_uniform_lsi_concrete_input
    {d N_c : ℕ} [NeZero N_c]
    (input : BalabanRGUniformLSIConcreteInput d N_c) :
    HaarLSITarget N_c := by
  exact
    haar_target_of_balaban_rg_uniform_lsi_frontier
      (balaban_rg_uniform_lsi_frontier_of_concrete_input d N_c input)

/-- Projection to the frontier package. -/
theorem frontier_package_of_balaban_rg_uniform_lsi_concrete_input
    {d N_c : ℕ} [NeZero N_c]
    (input : BalabanRGUniformLSIConcreteInput d N_c) :
    HaarLSIFrontierPackage d N_c := by
  exact
    frontier_package_of_balaban_rg_uniform_lsi_frontier
      (balaban_rg_uniform_lsi_frontier_of_concrete_input d N_c input)

end YangMills.ClayCore
