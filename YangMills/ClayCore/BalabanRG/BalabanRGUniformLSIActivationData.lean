import Mathlib
import YangMills.ClayCore.BalabanRG.BalabanRGUniformLSIPublicFacade

namespace YangMills.ClayCore

/-- Canonical public input packet for the current Balaban-RG / Haar-LSI lane:
it packages the transfer ingredient together with the preferred public live target. -/
structure BalabanRGUniformLSIActivationData (d N_c : ℕ) [NeZero N_c] : Prop where
  transfer : HaarLSIFromUniformLSITransfer N_c
  liveTarget : BalabanRGUniformLSILiveTarget d N_c

/-- Canonical input packet from the preferred public live target. -/
theorem balaban_rg_uniform_lsi_activation_data_of_live_target
    (d N_c : ℕ) [NeZero N_c]
    (tr : HaarLSIFromUniformLSITransfer N_c)
    (h : BalabanRGUniformLSILiveTarget d N_c) :
    BalabanRGUniformLSIActivationData d N_c := by
  exact ⟨tr, h⟩

/-- Canonical input packet from the direct uniform-theorem target. -/
theorem balaban_rg_uniform_lsi_activation_data_of_direct_uniform_theorem_target
    (d N_c : ℕ) [NeZero N_c]
    (tr : HaarLSIFromUniformLSITransfer N_c)
    (h : SpecialUnitaryDirectUniformLSITheoremTarget d N_c) :
    BalabanRGUniformLSIActivationData d N_c := by
  refine ⟨tr, ?_⟩
  exact (balaban_rg_uniform_lsi_live_target_iff_direct_uniform_theorem_target d N_c).2 h

/-- Canonical input packet from the old conditional target name. -/
theorem balaban_rg_uniform_lsi_activation_data_of_conditional_target
    (d N_c : ℕ) [NeZero N_c]
    (tr : HaarLSIFromUniformLSITransfer N_c)
    (h : BalabanRGUniformLSIConditionalTarget d N_c) :
    BalabanRGUniformLSIActivationData d N_c := by
  refine ⟨tr, ?_⟩
  exact balaban_rg_uniform_lsi_live_target_of_conditional_target h

/-- Canonical input packet from the old Haar-lane live target name. -/
theorem balaban_rg_uniform_lsi_activation_data_of_haar_lsi_live_target
    (d N_c : ℕ) [NeZero N_c]
    (tr : HaarLSIFromUniformLSITransfer N_c)
    (h : HaarLSILiveTarget d N_c) :
    BalabanRGUniformLSIActivationData d N_c := by
  refine ⟨tr, ?_⟩
  exact (balaban_rg_uniform_lsi_live_target_iff_haar_lsi_live_target d N_c).2 h

/-- Canonical input packet from an actual Balaban-RG package witness. -/
theorem balaban_rg_uniform_lsi_activation_data_of_pkg
    (d N_c : ℕ) [NeZero N_c]
    (tr : HaarLSIFromUniformLSITransfer N_c)
    (pkg : BalabanRGPackage d N_c) :
    BalabanRGUniformLSIActivationData d N_c := by
  refine ⟨tr, ?_⟩
  exact balaban_rg_uniform_lsi_live_target_of_pkg pkg

/-- Canonical input packet from the bare package-witness form. -/
theorem balaban_rg_uniform_lsi_activation_data_of_pkg_witness
    (d N_c : ℕ) [NeZero N_c]
    (tr : HaarLSIFromUniformLSITransfer N_c)
    (h : ∃ _ : BalabanRGPackage d N_c, True) :
    BalabanRGUniformLSIActivationData d N_c := by
  refine ⟨tr, ?_⟩
  exact balaban_rg_uniform_lsi_live_target_of_pkg_witness h

/-- Preferred public output facade from the canonical input packet. -/
theorem balaban_rg_uniform_lsi_public_facade_of_activation_data
    (d N_c : ℕ) [NeZero N_c]
    (data : BalabanRGUniformLSIActivationData d N_c) :
    BalabanRGUniformLSIPublicFacade d N_c := by
  exact balaban_rg_uniform_lsi_public_facade_of_live_target d N_c data.transfer data.liveTarget

/-- Bundled last-mile output from the canonical input packet. -/
theorem balaban_rg_uniform_lsi_last_mile_output_of_activation_data
    (d N_c : ℕ) [NeZero N_c]
    (data : BalabanRGUniformLSIActivationData d N_c) :
    BalabanRGUniformLSILastMileOutput d N_c := by
  exact balaban_rg_uniform_lsi_last_mile_output_of_live_target d N_c data.transfer data.liveTarget

/-- Structured closure package from the canonical input packet. -/
theorem balaban_rg_uniform_lsi_closure_package_of_activation_data
    (d N_c : ℕ) [NeZero N_c]
    (data : BalabanRGUniformLSIActivationData d N_c) :
    BalabanRGUniformLSIClosurePackage d N_c := by
  exact (balaban_rg_uniform_lsi_public_facade_of_activation_data d N_c data).closure

/-- Public equivalence registry from the canonical input packet. -/
theorem balaban_rg_uniform_lsi_equivalence_registry_of_activation_data
    (d N_c : ℕ) [NeZero N_c]
    (data : BalabanRGUniformLSIActivationData d N_c) :
    BalabanRGUniformLSIEquivalenceRegistry d N_c := by
  exact (balaban_rg_uniform_lsi_public_facade_of_activation_data d N_c data).registry

/-- Projection to the packaged transfer ingredient. -/
theorem transfer_of_balaban_rg_uniform_lsi_activation_data
    {d N_c : ℕ} [NeZero N_c]
    (data : BalabanRGUniformLSIActivationData d N_c) :
    HaarLSIFromUniformLSITransfer N_c := by
  exact data.transfer

/-- Projection to the preferred public live target. -/
theorem live_target_of_balaban_rg_uniform_lsi_activation_data
    {d N_c : ℕ} [NeZero N_c]
    (data : BalabanRGUniformLSIActivationData d N_c) :
    BalabanRGUniformLSILiveTarget d N_c := by
  exact data.liveTarget

/-- Projection to the direct uniform-theorem target. -/
theorem direct_uniform_theorem_target_of_activation_data
    {d N_c : ℕ} [NeZero N_c]
    (data : BalabanRGUniformLSIActivationData d N_c) :
    SpecialUnitaryDirectUniformLSITheoremTarget d N_c := by
  exact (balaban_rg_uniform_lsi_equivalence_registry d N_c).balabanToDirect.1 data.liveTarget

/-- Projection to the old conditional target name. -/
theorem conditional_target_of_activation_data
    {d N_c : ℕ} [NeZero N_c]
    (data : BalabanRGUniformLSIActivationData d N_c) :
    BalabanRGUniformLSIConditionalTarget d N_c := by
  exact (balaban_rg_uniform_lsi_equivalence_registry d N_c).balabanToConditional.1 data.liveTarget

/-- Projection to the old Haar-lane live target name. -/
theorem haar_lsi_live_target_of_activation_data
    {d N_c : ℕ} [NeZero N_c]
    (data : BalabanRGUniformLSIActivationData d N_c) :
    HaarLSILiveTarget d N_c := by
  exact (balaban_rg_uniform_lsi_equivalence_registry d N_c).balabanToHaar.1 data.liveTarget

/-- Projection to the bare package-witness form. -/
theorem pkg_witness_of_activation_data
    {d N_c : ℕ} [NeZero N_c]
    (data : BalabanRGUniformLSIActivationData d N_c) :
    ∃ _ : BalabanRGPackage d N_c, True := by
  exact (balaban_rg_uniform_lsi_equivalence_registry d N_c).balabanToPkgWitness.1 data.liveTarget

/-- Projection to the scale target through the canonical input packet. -/
theorem scale_target_of_activation_data
    {d N_c : ℕ} [NeZero N_c]
    (data : BalabanRGUniformLSIActivationData d N_c) :
    SpecialUnitaryScaleLSITarget d N_c := by
  exact (balaban_rg_uniform_lsi_closure_package_of_activation_data d N_c data).scaleTarget

/-- Projection to the Haar target through the canonical input packet. -/
theorem haar_target_of_activation_data
    {d N_c : ℕ} [NeZero N_c]
    (data : BalabanRGUniformLSIActivationData d N_c) :
    HaarLSITarget N_c := by
  exact (balaban_rg_uniform_lsi_closure_package_of_activation_data d N_c data).haarTarget

/-- Projection to the frontier package through the canonical input packet. -/
theorem frontier_package_of_activation_data
    {d N_c : ℕ} [NeZero N_c]
    (data : BalabanRGUniformLSIActivationData d N_c) :
    HaarLSIFrontierPackage d N_c := by
  exact (balaban_rg_uniform_lsi_closure_package_of_activation_data d N_c data).frontierPackage

end YangMills.ClayCore
