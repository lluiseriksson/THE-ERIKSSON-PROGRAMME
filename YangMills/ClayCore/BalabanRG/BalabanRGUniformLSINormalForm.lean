import Mathlib
import YangMills.ClayCore.BalabanRG.BalabanRGUniformLSILaneContract

namespace YangMills.ClayCore

/-- Coherence: the facade carried by any lane contract coincides with the
canonically reconstructed public facade of its activation data. -/
theorem balaban_rg_uniform_lsi_public_facade_eq_canonical_of_lane_contract
    {d N_c : ℕ} [NeZero N_c]
    (contract : BalabanRGUniformLSILaneContract d N_c) :
    contract.facade =
      balaban_rg_uniform_lsi_public_facade_of_activation_data d N_c contract.activation := by
  apply Subsingleton.elim

/-- Coherence: any lane contract is propositionally equal to the canonical
one reconstructed from its activation data. -/
theorem balaban_rg_uniform_lsi_lane_contract_eq_canonical_of_activation_data
    {d N_c : ℕ} [NeZero N_c]
    (contract : BalabanRGUniformLSILaneContract d N_c) :
    contract =
      balaban_rg_uniform_lsi_lane_contract_of_activation_data d N_c contract.activation := by
  apply Subsingleton.elim

/-- Logical normal form: the lane contract is equivalent to the canonical activation data. -/
theorem balaban_rg_uniform_lsi_lane_contract_iff_activation_data
    (d N_c : ℕ) [NeZero N_c] :
    BalabanRGUniformLSILaneContract d N_c ↔
      BalabanRGUniformLSIActivationData d N_c := by
  constructor
  · intro contract
    exact contract.activation
  · intro data
    exact balaban_rg_uniform_lsi_lane_contract_of_activation_data d N_c data

/-- Logical normal form: the lane contract is equivalent to transfer plus the preferred live target. -/
theorem balaban_rg_uniform_lsi_lane_contract_iff_live_target
    (d N_c : ℕ) [NeZero N_c] :
    BalabanRGUniformLSILaneContract d N_c ↔
      (HaarLSIFromUniformLSITransfer N_c ∧ BalabanRGUniformLSILiveTarget d N_c) := by
  constructor
  · intro contract
    exact ⟨contract.activation.transfer, contract.activation.liveTarget⟩
  · rintro ⟨tr, h⟩
    exact balaban_rg_uniform_lsi_lane_contract_of_live_target d N_c tr h

/-- Logical normal form: the lane contract is equivalent to transfer plus the direct uniform-theorem target. -/
theorem balaban_rg_uniform_lsi_lane_contract_iff_direct_uniform_theorem_target
    (d N_c : ℕ) [NeZero N_c] :
    BalabanRGUniformLSILaneContract d N_c ↔
      (HaarLSIFromUniformLSITransfer N_c ∧ SpecialUnitaryDirectUniformLSITheoremTarget d N_c) := by
  constructor
  · intro contract
    exact ⟨
      contract.activation.transfer,
      direct_uniform_theorem_target_of_activation_data contract.activation
    ⟩
  · rintro ⟨tr, h⟩
    exact balaban_rg_uniform_lsi_lane_contract_of_direct_uniform_theorem_target d N_c tr h

/-- Logical normal form: the lane contract is equivalent to transfer plus the old conditional target name. -/
theorem balaban_rg_uniform_lsi_lane_contract_iff_conditional_target
    (d N_c : ℕ) [NeZero N_c] :
    BalabanRGUniformLSILaneContract d N_c ↔
      (HaarLSIFromUniformLSITransfer N_c ∧ BalabanRGUniformLSIConditionalTarget d N_c) := by
  constructor
  · intro contract
    exact ⟨
      contract.activation.transfer,
      conditional_target_of_activation_data contract.activation
    ⟩
  · rintro ⟨tr, h⟩
    exact balaban_rg_uniform_lsi_lane_contract_of_conditional_target d N_c tr h

/-- Logical normal form: the lane contract is equivalent to transfer plus the old Haar-lane live target name. -/
theorem balaban_rg_uniform_lsi_lane_contract_iff_haar_lsi_live_target
    (d N_c : ℕ) [NeZero N_c] :
    BalabanRGUniformLSILaneContract d N_c ↔
      (HaarLSIFromUniformLSITransfer N_c ∧ HaarLSILiveTarget d N_c) := by
  constructor
  · intro contract
    exact ⟨
      contract.activation.transfer,
      haar_lsi_live_target_of_activation_data contract.activation
    ⟩
  · rintro ⟨tr, h⟩
    exact balaban_rg_uniform_lsi_lane_contract_of_haar_lsi_live_target d N_c tr h

/-- Logical normal form: the lane contract is equivalent to transfer plus the bare package-witness form. -/
theorem balaban_rg_uniform_lsi_lane_contract_iff_pkg_witness
    (d N_c : ℕ) [NeZero N_c] :
    BalabanRGUniformLSILaneContract d N_c ↔
      (HaarLSIFromUniformLSITransfer N_c ∧ (∃ pkg : BalabanRGPackage d N_c, True)) := by
  constructor
  · intro contract
    exact ⟨
      contract.activation.transfer,
      pkg_witness_of_activation_data contract.activation
    ⟩
  · rintro ⟨tr, h⟩
    exact balaban_rg_uniform_lsi_lane_contract_of_pkg_witness d N_c tr h

/-- The canonical activation packet recovered from the lane contract rebuilds the same lane contract. -/
theorem balaban_rg_uniform_lsi_lane_contract_round_trip
    {d N_c : ℕ} [NeZero N_c]
    (contract : BalabanRGUniformLSILaneContract d N_c) :
    balaban_rg_uniform_lsi_lane_contract_of_activation_data d N_c
      (activation_data_of_balaban_rg_uniform_lsi_lane_contract contract) = contract := by
  symm
  exact balaban_rg_uniform_lsi_lane_contract_eq_canonical_of_activation_data contract

end YangMills.ClayCore
