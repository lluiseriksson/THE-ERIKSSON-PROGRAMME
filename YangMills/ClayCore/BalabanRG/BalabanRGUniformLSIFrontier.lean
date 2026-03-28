import Mathlib
import YangMills.ClayCore.BalabanRG.BalabanRGUniformLSINormalForm

namespace YangMills.ClayCore

/-- Preferred short public entrypoint for the current Balaban-RG / Haar-LSI lane. -/
abbrev BalabanRGUniformLSIFrontier (d N_c : ℕ) [NeZero N_c] : Prop :=
  BalabanRGUniformLSILaneContract d N_c

/-- Short public entrypoint from the canonical activation data. -/
theorem balaban_rg_uniform_lsi_frontier_of_activation_data
    (d N_c : ℕ) [NeZero N_c]
    (data : BalabanRGUniformLSIActivationData d N_c) :
    BalabanRGUniformLSIFrontier d N_c := by
  exact balaban_rg_uniform_lsi_lane_contract_of_activation_data d N_c data

/-- Short public entrypoint from the preferred public live target. -/
theorem balaban_rg_uniform_lsi_frontier_of_live_target
    (d N_c : ℕ) [NeZero N_c]
    (tr : HaarLSIFromUniformLSITransfer N_c)
    (h : BalabanRGUniformLSILiveTarget d N_c) :
    BalabanRGUniformLSIFrontier d N_c := by
  exact balaban_rg_uniform_lsi_lane_contract_of_live_target d N_c tr h

/-- Short public entrypoint from the direct uniform-theorem target. -/
theorem balaban_rg_uniform_lsi_frontier_of_direct_uniform_theorem_target
    (d N_c : ℕ) [NeZero N_c]
    (tr : HaarLSIFromUniformLSITransfer N_c)
    (h : SpecialUnitaryDirectUniformLSITheoremTarget d N_c) :
    BalabanRGUniformLSIFrontier d N_c := by
  exact balaban_rg_uniform_lsi_lane_contract_of_direct_uniform_theorem_target d N_c tr h

/-- Short public entrypoint from the old conditional target name. -/
theorem balaban_rg_uniform_lsi_frontier_of_conditional_target
    (d N_c : ℕ) [NeZero N_c]
    (tr : HaarLSIFromUniformLSITransfer N_c)
    (h : BalabanRGUniformLSIConditionalTarget d N_c) :
    BalabanRGUniformLSIFrontier d N_c := by
  exact balaban_rg_uniform_lsi_lane_contract_of_conditional_target d N_c tr h

/-- Short public entrypoint from the old Haar-lane live target name. -/
theorem balaban_rg_uniform_lsi_frontier_of_haar_lsi_live_target
    (d N_c : ℕ) [NeZero N_c]
    (tr : HaarLSIFromUniformLSITransfer N_c)
    (h : HaarLSILiveTarget d N_c) :
    BalabanRGUniformLSIFrontier d N_c := by
  exact balaban_rg_uniform_lsi_lane_contract_of_haar_lsi_live_target d N_c tr h

/-- Short public entrypoint from an actual Balaban-RG package witness. -/
theorem balaban_rg_uniform_lsi_frontier_of_pkg
    (d N_c : ℕ) [NeZero N_c]
    (tr : HaarLSIFromUniformLSITransfer N_c)
    (pkg : BalabanRGPackage d N_c) :
    BalabanRGUniformLSIFrontier d N_c := by
  exact balaban_rg_uniform_lsi_lane_contract_of_pkg d N_c tr pkg

/-- Short public entrypoint from the bare package-witness form. -/
theorem balaban_rg_uniform_lsi_frontier_of_pkg_witness
    (d N_c : ℕ) [NeZero N_c]
    (tr : HaarLSIFromUniformLSITransfer N_c)
    (h : ∃ _ : BalabanRGPackage d N_c, True) :
    BalabanRGUniformLSIFrontier d N_c := by
  exact balaban_rg_uniform_lsi_lane_contract_of_pkg_witness d N_c tr h

/-- Projection to the canonical activation data. -/
theorem activation_data_of_balaban_rg_uniform_lsi_frontier
    {d N_c : ℕ} [NeZero N_c]
    (frontier : BalabanRGUniformLSIFrontier d N_c) :
    BalabanRGUniformLSIActivationData d N_c := by
  exact activation_data_of_balaban_rg_uniform_lsi_lane_contract frontier

/-- Projection to the canonical public facade. -/
theorem public_facade_of_balaban_rg_uniform_lsi_frontier
    {d N_c : ℕ} [NeZero N_c]
    (frontier : BalabanRGUniformLSIFrontier d N_c) :
    BalabanRGUniformLSIPublicFacade d N_c := by
  exact public_facade_of_balaban_rg_uniform_lsi_lane_contract frontier

/-- Projection to the structured closure package. -/
theorem closure_package_of_balaban_rg_uniform_lsi_frontier
    {d N_c : ℕ} [NeZero N_c]
    (frontier : BalabanRGUniformLSIFrontier d N_c) :
    BalabanRGUniformLSIClosurePackage d N_c := by
  exact closure_package_of_balaban_rg_uniform_lsi_lane_contract frontier

/-- Projection to the equivalence registry. -/
theorem equivalence_registry_of_balaban_rg_uniform_lsi_frontier
    {d N_c : ℕ} [NeZero N_c]
    (frontier : BalabanRGUniformLSIFrontier d N_c) :
    BalabanRGUniformLSIEquivalenceRegistry d N_c := by
  exact equivalence_registry_of_balaban_rg_uniform_lsi_lane_contract frontier

/-- Projection to the bundled last-mile output. -/
theorem last_mile_output_of_balaban_rg_uniform_lsi_frontier
    {d N_c : ℕ} [NeZero N_c]
    (frontier : BalabanRGUniformLSIFrontier d N_c) :
    BalabanRGUniformLSILastMileOutput d N_c := by
  exact last_mile_output_of_balaban_rg_uniform_lsi_lane_contract frontier

/-- Projection to the scale target. -/
theorem scale_target_of_balaban_rg_uniform_lsi_frontier
    {d N_c : ℕ} [NeZero N_c]
    (frontier : BalabanRGUniformLSIFrontier d N_c) :
    SpecialUnitaryScaleLSITarget d N_c := by
  exact scale_target_of_balaban_rg_uniform_lsi_lane_contract frontier

/-- Projection to the Haar target. -/
theorem haar_target_of_balaban_rg_uniform_lsi_frontier
    {d N_c : ℕ} [NeZero N_c]
    (frontier : BalabanRGUniformLSIFrontier d N_c) :
    HaarLSITarget N_c := by
  exact haar_target_of_balaban_rg_uniform_lsi_lane_contract frontier

/-- Projection to the frontier package. -/
theorem frontier_package_of_balaban_rg_uniform_lsi_frontier
    {d N_c : ℕ} [NeZero N_c]
    (frontier : BalabanRGUniformLSIFrontier d N_c) :
    HaarLSIFrontierPackage d N_c := by
  exact frontier_package_of_balaban_rg_uniform_lsi_lane_contract frontier

/-- Logical normal form: the short public frontier is equivalent to the canonical activation data. -/
theorem balaban_rg_uniform_lsi_frontier_iff_activation_data
    (d N_c : ℕ) [NeZero N_c] :
    BalabanRGUniformLSIFrontier d N_c ↔
      BalabanRGUniformLSIActivationData d N_c := by
  exact balaban_rg_uniform_lsi_lane_contract_iff_activation_data d N_c

/-- Logical normal form: the short public frontier is equivalent to transfer plus the preferred live target. -/
theorem balaban_rg_uniform_lsi_frontier_iff_live_target
    (d N_c : ℕ) [NeZero N_c] :
    BalabanRGUniformLSIFrontier d N_c ↔
      (HaarLSIFromUniformLSITransfer N_c ∧ BalabanRGUniformLSILiveTarget d N_c) := by
  exact balaban_rg_uniform_lsi_lane_contract_iff_live_target d N_c

/-- Logical normal form: the short public frontier is equivalent to transfer plus the direct uniform-theorem target. -/
theorem balaban_rg_uniform_lsi_frontier_iff_direct_uniform_theorem_target
    (d N_c : ℕ) [NeZero N_c] :
    BalabanRGUniformLSIFrontier d N_c ↔
      (HaarLSIFromUniformLSITransfer N_c ∧ SpecialUnitaryDirectUniformLSITheoremTarget d N_c) := by
  exact balaban_rg_uniform_lsi_lane_contract_iff_direct_uniform_theorem_target d N_c

/-- Logical normal form: the short public frontier is equivalent to transfer plus the old conditional target name. -/
theorem balaban_rg_uniform_lsi_frontier_iff_conditional_target
    (d N_c : ℕ) [NeZero N_c] :
    BalabanRGUniformLSIFrontier d N_c ↔
      (HaarLSIFromUniformLSITransfer N_c ∧ BalabanRGUniformLSIConditionalTarget d N_c) := by
  exact balaban_rg_uniform_lsi_lane_contract_iff_conditional_target d N_c

/-- Logical normal form: the short public frontier is equivalent to transfer plus the old Haar-lane live target name. -/
theorem balaban_rg_uniform_lsi_frontier_iff_haar_lsi_live_target
    (d N_c : ℕ) [NeZero N_c] :
    BalabanRGUniformLSIFrontier d N_c ↔
      (HaarLSIFromUniformLSITransfer N_c ∧ HaarLSILiveTarget d N_c) := by
  exact balaban_rg_uniform_lsi_lane_contract_iff_haar_lsi_live_target d N_c

/-- Logical normal form: the short public frontier is equivalent to transfer plus the bare package-witness form. -/
theorem balaban_rg_uniform_lsi_frontier_iff_pkg_witness
    (d N_c : ℕ) [NeZero N_c] :
    BalabanRGUniformLSIFrontier d N_c ↔
      (HaarLSIFromUniformLSITransfer N_c ∧ (∃ _ : BalabanRGPackage d N_c, True)) := by
  exact balaban_rg_uniform_lsi_lane_contract_iff_pkg_witness d N_c

/-- Coherence: the short public frontier is propositionally equal to the canonical one reconstructed from its activation data. -/
theorem balaban_rg_uniform_lsi_frontier_eq_canonical_of_activation_data
    {d N_c : ℕ} [NeZero N_c]
    (frontier : BalabanRGUniformLSIFrontier d N_c) :
    frontier =
      balaban_rg_uniform_lsi_frontier_of_activation_data d N_c
        (activation_data_of_balaban_rg_uniform_lsi_frontier frontier) := by
  exact balaban_rg_uniform_lsi_lane_contract_eq_canonical_of_activation_data frontier

/-- Coherence: the facade carried by the short public frontier is the canonical one reconstructed from its activation data. -/
theorem balaban_rg_uniform_lsi_public_facade_eq_canonical_of_frontier
    {d N_c : ℕ} [NeZero N_c]
    (frontier : BalabanRGUniformLSIFrontier d N_c) :
    public_facade_of_balaban_rg_uniform_lsi_frontier frontier =
      balaban_rg_uniform_lsi_public_facade_of_activation_data d N_c
        (activation_data_of_balaban_rg_uniform_lsi_frontier frontier) := by
  exact balaban_rg_uniform_lsi_public_facade_eq_canonical_of_lane_contract frontier

end YangMills.ClayCore
