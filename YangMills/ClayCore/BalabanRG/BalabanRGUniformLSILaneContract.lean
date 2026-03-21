import Mathlib
import YangMills.ClayCore.BalabanRG.BalabanRGUniformLSIActivationData

namespace YangMills.ClayCore

/-- Canonical trunk-facing contract for the current Balaban-RG / Haar-LSI lane:
it carries both the canonical input packet and the canonical output facade. -/
structure BalabanRGUniformLSILaneContract (d N_c : ℕ) [NeZero N_c] : Prop where
  activation : BalabanRGUniformLSIActivationData d N_c
  facade : BalabanRGUniformLSIPublicFacade d N_c

/-- Canonical lane contract from the canonical activation data. -/
theorem balaban_rg_uniform_lsi_lane_contract_of_activation_data
    (d N_c : ℕ) [NeZero N_c]
    (data : BalabanRGUniformLSIActivationData d N_c) :
    BalabanRGUniformLSILaneContract d N_c := by
  exact ⟨data, balaban_rg_uniform_lsi_public_facade_of_activation_data d N_c data⟩

/-- Canonical lane contract from the preferred public live target. -/
theorem balaban_rg_uniform_lsi_lane_contract_of_live_target
    (d N_c : ℕ) [NeZero N_c]
    (tr : HaarLSIFromUniformLSITransfer N_c)
    (h : BalabanRGUniformLSILiveTarget d N_c) :
    BalabanRGUniformLSILaneContract d N_c := by
  exact
    balaban_rg_uniform_lsi_lane_contract_of_activation_data d N_c
      (balaban_rg_uniform_lsi_activation_data_of_live_target d N_c tr h)

/-- Canonical lane contract from the direct uniform-theorem target. -/
theorem balaban_rg_uniform_lsi_lane_contract_of_direct_uniform_theorem_target
    (d N_c : ℕ) [NeZero N_c]
    (tr : HaarLSIFromUniformLSITransfer N_c)
    (h : SpecialUnitaryDirectUniformLSITheoremTarget d N_c) :
    BalabanRGUniformLSILaneContract d N_c := by
  exact
    balaban_rg_uniform_lsi_lane_contract_of_activation_data d N_c
      (balaban_rg_uniform_lsi_activation_data_of_direct_uniform_theorem_target d N_c tr h)

/-- Canonical lane contract from the old conditional target name. -/
theorem balaban_rg_uniform_lsi_lane_contract_of_conditional_target
    (d N_c : ℕ) [NeZero N_c]
    (tr : HaarLSIFromUniformLSITransfer N_c)
    (h : BalabanRGUniformLSIConditionalTarget d N_c) :
    BalabanRGUniformLSILaneContract d N_c := by
  exact
    balaban_rg_uniform_lsi_lane_contract_of_activation_data d N_c
      (balaban_rg_uniform_lsi_activation_data_of_conditional_target d N_c tr h)

/-- Canonical lane contract from the old Haar-lane live target name. -/
theorem balaban_rg_uniform_lsi_lane_contract_of_haar_lsi_live_target
    (d N_c : ℕ) [NeZero N_c]
    (tr : HaarLSIFromUniformLSITransfer N_c)
    (h : HaarLSILiveTarget d N_c) :
    BalabanRGUniformLSILaneContract d N_c := by
  exact
    balaban_rg_uniform_lsi_lane_contract_of_activation_data d N_c
      (balaban_rg_uniform_lsi_activation_data_of_haar_lsi_live_target d N_c tr h)

/-- Canonical lane contract from an actual Balaban-RG package witness. -/
theorem balaban_rg_uniform_lsi_lane_contract_of_pkg
    (d N_c : ℕ) [NeZero N_c]
    (tr : HaarLSIFromUniformLSITransfer N_c)
    (pkg : BalabanRGPackage d N_c) :
    BalabanRGUniformLSILaneContract d N_c := by
  exact
    balaban_rg_uniform_lsi_lane_contract_of_activation_data d N_c
      (balaban_rg_uniform_lsi_activation_data_of_pkg d N_c tr pkg)

/-- Canonical lane contract from the bare package-witness form. -/
theorem balaban_rg_uniform_lsi_lane_contract_of_pkg_witness
    (d N_c : ℕ) [NeZero N_c]
    (tr : HaarLSIFromUniformLSITransfer N_c)
    (h : ∃ pkg : BalabanRGPackage d N_c, True) :
    BalabanRGUniformLSILaneContract d N_c := by
  exact
    balaban_rg_uniform_lsi_lane_contract_of_activation_data d N_c
      (balaban_rg_uniform_lsi_activation_data_of_pkg_witness d N_c tr h)

/-- Projection to the canonical activation data. -/
theorem activation_data_of_balaban_rg_uniform_lsi_lane_contract
    {d N_c : ℕ} [NeZero N_c]
    (contract : BalabanRGUniformLSILaneContract d N_c) :
    BalabanRGUniformLSIActivationData d N_c := by
  exact contract.activation

/-- Projection to the canonical public facade. -/
theorem public_facade_of_balaban_rg_uniform_lsi_lane_contract
    {d N_c : ℕ} [NeZero N_c]
    (contract : BalabanRGUniformLSILaneContract d N_c) :
    BalabanRGUniformLSIPublicFacade d N_c := by
  exact contract.facade

/-- Projection to the transfer ingredient. -/
theorem transfer_of_balaban_rg_uniform_lsi_lane_contract
    {d N_c : ℕ} [NeZero N_c]
    (contract : BalabanRGUniformLSILaneContract d N_c) :
    HaarLSIFromUniformLSITransfer N_c := by
  exact contract.activation.transfer

/-- Projection to the preferred public live target. -/
theorem live_target_of_balaban_rg_uniform_lsi_lane_contract
    {d N_c : ℕ} [NeZero N_c]
    (contract : BalabanRGUniformLSILaneContract d N_c) :
    BalabanRGUniformLSILiveTarget d N_c := by
  exact contract.activation.liveTarget

/-- Projection to the structured closure package. -/
theorem closure_package_of_balaban_rg_uniform_lsi_lane_contract
    {d N_c : ℕ} [NeZero N_c]
    (contract : BalabanRGUniformLSILaneContract d N_c) :
    BalabanRGUniformLSIClosurePackage d N_c := by
  exact contract.facade.closure

/-- Projection to the equivalence registry. -/
theorem equivalence_registry_of_balaban_rg_uniform_lsi_lane_contract
    {d N_c : ℕ} [NeZero N_c]
    (contract : BalabanRGUniformLSILaneContract d N_c) :
    BalabanRGUniformLSIEquivalenceRegistry d N_c := by
  exact contract.facade.registry

/-- Projection to the bundled last-mile output. -/
theorem last_mile_output_of_balaban_rg_uniform_lsi_lane_contract
    {d N_c : ℕ} [NeZero N_c]
    (contract : BalabanRGUniformLSILaneContract d N_c) :
    BalabanRGUniformLSILastMileOutput d N_c := by
  exact balaban_rg_uniform_lsi_last_mile_output_of_activation_data d N_c contract.activation

/-- Projection to the scale target. -/
theorem scale_target_of_balaban_rg_uniform_lsi_lane_contract
    {d N_c : ℕ} [NeZero N_c]
    (contract : BalabanRGUniformLSILaneContract d N_c) :
    SpecialUnitaryScaleLSITarget d N_c := by
  exact contract.facade.closure.scaleTarget

/-- Projection to the Haar target. -/
theorem haar_target_of_balaban_rg_uniform_lsi_lane_contract
    {d N_c : ℕ} [NeZero N_c]
    (contract : BalabanRGUniformLSILaneContract d N_c) :
    HaarLSITarget N_c := by
  exact contract.facade.closure.haarTarget

/-- Projection to the frontier package. -/
theorem frontier_package_of_balaban_rg_uniform_lsi_lane_contract
    {d N_c : ℕ} [NeZero N_c]
    (contract : BalabanRGUniformLSILaneContract d N_c) :
    HaarLSIFrontierPackage d N_c := by
  exact contract.facade.closure.frontierPackage

/-- Projection to the direct uniform-theorem target. -/
theorem direct_uniform_theorem_target_of_balaban_rg_uniform_lsi_lane_contract
    {d N_c : ℕ} [NeZero N_c]
    (contract : BalabanRGUniformLSILaneContract d N_c) :
    SpecialUnitaryDirectUniformLSITheoremTarget d N_c := by
  exact direct_uniform_theorem_target_of_activation_data contract.activation

/-- Projection to the old conditional target name. -/
theorem conditional_target_of_balaban_rg_uniform_lsi_lane_contract
    {d N_c : ℕ} [NeZero N_c]
    (contract : BalabanRGUniformLSILaneContract d N_c) :
    BalabanRGUniformLSIConditionalTarget d N_c := by
  exact conditional_target_of_activation_data contract.activation

/-- Projection to the old Haar-lane live target name. -/
theorem haar_lsi_live_target_of_balaban_rg_uniform_lsi_lane_contract
    {d N_c : ℕ} [NeZero N_c]
    (contract : BalabanRGUniformLSILaneContract d N_c) :
    HaarLSILiveTarget d N_c := by
  exact haar_lsi_live_target_of_activation_data contract.activation

/-- Projection to the bare package-witness form. -/
theorem pkg_witness_of_balaban_rg_uniform_lsi_lane_contract
    {d N_c : ℕ} [NeZero N_c]
    (contract : BalabanRGUniformLSILaneContract d N_c) :
    ∃ pkg : BalabanRGPackage d N_c, True := by
  exact pkg_witness_of_activation_data contract.activation

end YangMills.ClayCore
