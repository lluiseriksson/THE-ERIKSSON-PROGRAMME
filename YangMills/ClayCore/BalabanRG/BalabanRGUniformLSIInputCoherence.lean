import Mathlib
import YangMills.ClayCore.BalabanRG.BalabanRGUniformLSIDirectInput

namespace YangMills.ClayCore

/-- Cross-normal form: direct input is exactly transfer plus the preferred live target. -/
theorem balaban_rg_uniform_lsi_direct_input_iff_live_target
    (d N_c : ℕ) [NeZero N_c] :
    BalabanRGUniformLSIDirectInput d N_c ↔
      (HaarLSIFromUniformLSITransfer N_c ∧ BalabanRGUniformLSILiveTarget d N_c) := by
  constructor
  · intro input
    exact
      ⟨transfer_of_balaban_rg_uniform_lsi_direct_input input,
        live_target_of_balaban_rg_uniform_lsi_direct_input input⟩
  · intro h
    exact
      balaban_rg_uniform_lsi_direct_input_of_activation_data
        (balaban_rg_uniform_lsi_activation_data_of_live_target d N_c h.1 h.2)

/-- Cross-normal form: direct input is exactly transfer plus the bare package-witness surface. -/
theorem balaban_rg_uniform_lsi_direct_input_iff_pkg_witness
    (d N_c : ℕ) [NeZero N_c] :
    BalabanRGUniformLSIDirectInput d N_c ↔
      (HaarLSIFromUniformLSITransfer N_c ∧ ∃ _ : BalabanRGPackage d N_c, True) := by
  constructor
  · intro input
    exact
      ⟨transfer_of_balaban_rg_uniform_lsi_direct_input input,
        pkg_witness_of_balaban_rg_uniform_lsi_direct_input input⟩
  · intro h
    exact balaban_rg_uniform_lsi_direct_input_of_pkg_witness d N_c h.1 h.2

/-- Cross-normal form: concrete input is exactly transfer plus the preferred live target. -/
theorem balaban_rg_uniform_lsi_concrete_input_iff_live_target
    (d N_c : ℕ) [NeZero N_c] :
    BalabanRGUniformLSIConcreteInput d N_c ↔
      (HaarLSIFromUniformLSITransfer N_c ∧ BalabanRGUniformLSILiveTarget d N_c) := by
  constructor
  · intro input
    exact
      ⟨transfer_of_balaban_rg_uniform_lsi_concrete_input input,
        live_target_of_balaban_rg_uniform_lsi_concrete_input input⟩
  · intro h
    exact
      balaban_rg_uniform_lsi_concrete_input_of_activation_data
        (balaban_rg_uniform_lsi_activation_data_of_live_target d N_c h.1 h.2)

/-- Cross-normal form: concrete input is exactly transfer plus the direct uniform-theorem target. -/
theorem balaban_rg_uniform_lsi_concrete_input_iff_direct_uniform_theorem_target
    (d N_c : ℕ) [NeZero N_c] :
    BalabanRGUniformLSIConcreteInput d N_c ↔
      (HaarLSIFromUniformLSITransfer N_c ∧
        SpecialUnitaryDirectUniformLSITheoremTarget d N_c) := by
  constructor
  · intro input
    exact
      ⟨transfer_of_balaban_rg_uniform_lsi_concrete_input input,
        direct_uniform_theorem_target_of_activation_data
          (balaban_rg_uniform_lsi_activation_data_of_concrete_input d N_c input)⟩
  · intro h
    exact
      balaban_rg_uniform_lsi_concrete_input_of_activation_data
        (balaban_rg_uniform_lsi_activation_data_of_direct_uniform_theorem_target
          d N_c h.1 h.2)

/-- Round-trip coherence: direct → concrete → direct is canonically the identity. -/
theorem balaban_rg_uniform_lsi_direct_input_of_concrete_input_of_direct_input_eq_canonical
    {d N_c : ℕ} [NeZero N_c]
    (input : BalabanRGUniformLSIDirectInput d N_c) :
    balaban_rg_uniform_lsi_direct_input_of_concrete_input
      (balaban_rg_uniform_lsi_concrete_input_of_direct_input d N_c input) = input := by
  apply Subsingleton.elim

/-- Round-trip coherence: concrete → direct → concrete is canonically the identity. -/
theorem balaban_rg_uniform_lsi_concrete_input_of_direct_input_of_concrete_input_eq_canonical
    {d N_c : ℕ} [NeZero N_c]
    (input : BalabanRGUniformLSIConcreteInput d N_c) :
    balaban_rg_uniform_lsi_concrete_input_of_direct_input d N_c
      (balaban_rg_uniform_lsi_direct_input_of_concrete_input input) = input := by
  apply Subsingleton.elim

/-- Round-trip coherence: frontier → direct → frontier is canonically the identity. -/
theorem balaban_rg_uniform_lsi_frontier_of_direct_input_of_frontier_eq_canonical
    {d N_c : ℕ} [NeZero N_c]
    (frontier : BalabanRGUniformLSIFrontier d N_c) :
    balaban_rg_uniform_lsi_frontier_of_direct_input d N_c
      (balaban_rg_uniform_lsi_direct_input_of_activation_data
        (activation_data_of_balaban_rg_uniform_lsi_frontier frontier)) = frontier := by
  apply Subsingleton.elim

/-- Round-trip coherence: frontier → concrete → frontier is canonically the identity. -/
theorem balaban_rg_uniform_lsi_frontier_of_concrete_input_of_frontier_eq_canonical
    {d N_c : ℕ} [NeZero N_c]
    (frontier : BalabanRGUniformLSIFrontier d N_c) :
    balaban_rg_uniform_lsi_frontier_of_concrete_input d N_c
      (balaban_rg_uniform_lsi_concrete_input_of_activation_data
        (activation_data_of_balaban_rg_uniform_lsi_frontier frontier)) = frontier := by
  apply Subsingleton.elim

/-- Round-trip coherence: activation → direct → activation is canonically the identity. -/
theorem balaban_rg_uniform_lsi_activation_data_of_direct_input_of_activation_data_eq_canonical
    {d N_c : ℕ} [NeZero N_c]
    (data : BalabanRGUniformLSIActivationData d N_c) :
    activation_data_of_balaban_rg_uniform_lsi_direct_input d N_c
      (balaban_rg_uniform_lsi_direct_input_of_activation_data data) = data := by
  apply Subsingleton.elim

/-- Round-trip coherence: activation → concrete → activation is canonically the identity. -/
theorem balaban_rg_uniform_lsi_activation_data_of_concrete_input_of_activation_data_eq_canonical
    {d N_c : ℕ} [NeZero N_c]
    (data : BalabanRGUniformLSIActivationData d N_c) :
    balaban_rg_uniform_lsi_activation_data_of_concrete_input d N_c
      (balaban_rg_uniform_lsi_concrete_input_of_activation_data data) = data := by
  apply Subsingleton.elim

end YangMills.ClayCore
