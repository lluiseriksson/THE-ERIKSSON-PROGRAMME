import Mathlib
import YangMills.ClayCore.BalabanRG.PhysicalRGRatesFrontier
import YangMills.ClayCore.BalabanRG.BalabanRGUniformLSIFrontier

namespace YangMills.ClayCore

/-- Direct quantitative frontier for the public Balaban-RG / Haar-LSI lane:
it packages the transfer ingredient together with the direct quantitative
`PhysicalRGRates` frontier. -/
structure BalabanRGUniformLSIQuantitativeFrontier
    (d N_c : ℕ) [NeZero N_c] : Prop where
  transfer : HaarLSIFromUniformLSITransfer N_c
  ratesFrontier : PhysicalRGRatesFrontier d N_c

/-- Canonical quantitative frontier from the transfer ingredient and a quantitative rates frontier. -/
theorem balaban_rg_uniform_lsi_quantitative_frontier_of_rates_frontier
    (d N_c : ℕ) [NeZero N_c]
    (tr : HaarLSIFromUniformLSITransfer N_c)
    (ratesFrontier : PhysicalRGRatesFrontier d N_c) :
    BalabanRGUniformLSIQuantitativeFrontier d N_c := by
  exact ⟨tr, ratesFrontier⟩

/-- Canonical quantitative frontier from the transfer ingredient and the preferred direct quantitative witness. -/
theorem balaban_rg_uniform_lsi_quantitative_frontier_of_witness
    (d N_c : ℕ) [NeZero N_c]
    (tr : HaarLSIFromUniformLSITransfer N_c) :
    BalabanRGUniformLSIQuantitativeFrontier d N_c := by
  exact ⟨tr, physical_rg_rates_frontier_of_witness d N_c⟩

/-- Projection to the transfer ingredient. -/
theorem transfer_of_balaban_rg_uniform_lsi_quantitative_frontier
    {d N_c : ℕ} [NeZero N_c]
    (frontier : BalabanRGUniformLSIQuantitativeFrontier d N_c) :
    HaarLSIFromUniformLSITransfer N_c := by
  exact frontier.transfer

/-- Projection to the quantitative rates frontier. -/
theorem physical_rg_rates_frontier_of_balaban_rg_uniform_lsi_quantitative_frontier
    {d N_c : ℕ} [NeZero N_c]
    (frontier : BalabanRGUniformLSIQuantitativeFrontier d N_c) :
    PhysicalRGRatesFrontier d N_c := by
  exact frontier.ratesFrontier

/-- Recover a Balaban-RG package from the quantitative Haar-LSI frontier. -/
theorem balaban_rg_package_of_balaban_rg_uniform_lsi_quantitative_frontier
    {d N_c : ℕ} [NeZero N_c]
    (frontier : BalabanRGUniformLSIQuantitativeFrontier d N_c) :
    BalabanRGPackage d N_c := by
  exact balaban_rg_package_of_physical_rg_rates_frontier frontier.ratesFrontier

/-- Recover uniform LSI from the quantitative Haar-LSI frontier. -/
theorem uniform_lsi_of_balaban_rg_uniform_lsi_quantitative_frontier
    {d N_c : ℕ} [NeZero N_c]
    (frontier : BalabanRGUniformLSIQuantitativeFrontier d N_c) :
    ∃ c > 0, ClayCoreLSI d N_c c := by
  exact uniform_lsi_of_physical_rg_rates_frontier frontier.ratesFrontier

/-- Recover the canonical activation data from the quantitative Haar-LSI frontier. -/
theorem balaban_rg_uniform_lsi_activation_data_of_quantitative_frontier
    (d N_c : ℕ) [NeZero N_c]
    (frontier : BalabanRGUniformLSIQuantitativeFrontier d N_c) :
    BalabanRGUniformLSIActivationData d N_c := by
  exact
    balaban_rg_uniform_lsi_activation_data_of_pkg d N_c
      frontier.transfer
      (balaban_rg_package_of_balaban_rg_uniform_lsi_quantitative_frontier frontier)

/-- Recover the canonical trunk-facing lane contract from the quantitative Haar-LSI frontier. -/
theorem balaban_rg_uniform_lsi_lane_contract_of_quantitative_frontier
    (d N_c : ℕ) [NeZero N_c]
    (frontier : BalabanRGUniformLSIQuantitativeFrontier d N_c) :
    BalabanRGUniformLSILaneContract d N_c := by
  exact
    balaban_rg_uniform_lsi_lane_contract_of_pkg d N_c
      frontier.transfer
      (balaban_rg_package_of_balaban_rg_uniform_lsi_quantitative_frontier frontier)

/-- Recover the preferred short public Haar-LSI frontier from the quantitative Haar-LSI frontier. -/
theorem balaban_rg_uniform_lsi_frontier_of_quantitative_frontier
    (d N_c : ℕ) [NeZero N_c]
    (frontier : BalabanRGUniformLSIQuantitativeFrontier d N_c) :
    BalabanRGUniformLSIFrontier d N_c := by
  exact
    balaban_rg_uniform_lsi_frontier_of_pkg d N_c
      frontier.transfer
      (balaban_rg_package_of_balaban_rg_uniform_lsi_quantitative_frontier frontier)

/-- Recover the preferred public facade from the quantitative Haar-LSI frontier. -/
theorem balaban_rg_uniform_lsi_public_facade_of_quantitative_frontier
    (d N_c : ℕ) [NeZero N_c]
    (frontier : BalabanRGUniformLSIQuantitativeFrontier d N_c) :
    BalabanRGUniformLSIPublicFacade d N_c := by
  exact
    balaban_rg_uniform_lsi_public_facade_of_pkg d N_c
      frontier.transfer
      (balaban_rg_package_of_balaban_rg_uniform_lsi_quantitative_frontier frontier)

/-- Recover the structured closure package from the quantitative Haar-LSI frontier. -/
theorem balaban_rg_uniform_lsi_closure_package_of_quantitative_frontier
    (d N_c : ℕ) [NeZero N_c]
    (frontier : BalabanRGUniformLSIQuantitativeFrontier d N_c) :
    BalabanRGUniformLSIClosurePackage d N_c := by
  exact
    closure_package_of_balaban_rg_uniform_lsi_public_facade
      (balaban_rg_uniform_lsi_public_facade_of_quantitative_frontier d N_c frontier)

/-- Recover the public equivalence registry from the quantitative Haar-LSI frontier. -/
theorem balaban_rg_uniform_lsi_equivalence_registry_of_quantitative_frontier
    (d N_c : ℕ) [NeZero N_c]
    (frontier : BalabanRGUniformLSIQuantitativeFrontier d N_c) :
    BalabanRGUniformLSIEquivalenceRegistry d N_c := by
  exact
    equivalence_registry_of_balaban_rg_uniform_lsi_public_facade
      (balaban_rg_uniform_lsi_public_facade_of_quantitative_frontier d N_c frontier)

/-- Projection to the scale target through the quantitative Haar-LSI frontier. -/
theorem scale_target_of_balaban_rg_uniform_lsi_quantitative_frontier
    {d N_c : ℕ} [NeZero N_c]
    (frontier : BalabanRGUniformLSIQuantitativeFrontier d N_c) :
    SpecialUnitaryScaleLSITarget d N_c := by
  exact
    scale_target_of_balaban_rg_uniform_lsi_public_facade
      (balaban_rg_uniform_lsi_public_facade_of_quantitative_frontier d N_c frontier)

/-- Projection to the Haar target through the quantitative Haar-LSI frontier. -/
theorem haar_target_of_balaban_rg_uniform_lsi_quantitative_frontier
    {d N_c : ℕ} [NeZero N_c]
    (frontier : BalabanRGUniformLSIQuantitativeFrontier d N_c) :
    HaarLSITarget N_c := by
  exact
    haar_target_of_balaban_rg_uniform_lsi_public_facade
      (balaban_rg_uniform_lsi_public_facade_of_quantitative_frontier d N_c frontier)

/-- Projection to the frontier package through the quantitative Haar-LSI frontier. -/
theorem frontier_package_of_balaban_rg_uniform_lsi_quantitative_frontier
    {d N_c : ℕ} [NeZero N_c]
    (frontier : BalabanRGUniformLSIQuantitativeFrontier d N_c) :
    HaarLSIFrontierPackage d N_c := by
  exact
    frontier_package_of_balaban_rg_uniform_lsi_public_facade
      (balaban_rg_uniform_lsi_public_facade_of_quantitative_frontier d N_c frontier)

/-- Logical normal form: the quantitative Haar-LSI frontier is equivalent to the pair
consisting of the transfer ingredient and the quantitative rates frontier. -/
theorem balaban_rg_uniform_lsi_quantitative_frontier_iff_pair
    (d N_c : ℕ) [NeZero N_c] :
    BalabanRGUniformLSIQuantitativeFrontier d N_c ↔
      (HaarLSIFromUniformLSITransfer N_c ∧ PhysicalRGRatesFrontier d N_c) := by
  constructor
  · intro frontier
    exact ⟨frontier.transfer, frontier.ratesFrontier⟩
  · intro h
    exact balaban_rg_uniform_lsi_quantitative_frontier_of_rates_frontier d N_c h.1 h.2

/-- Coherence: the quantitative Haar-LSI frontier is propositionally equal to the canonical one
reconstructed from its pair surface. -/
theorem balaban_rg_uniform_lsi_quantitative_frontier_eq_canonical_of_pair
    {d N_c : ℕ} [NeZero N_c]
    (frontier : BalabanRGUniformLSIQuantitativeFrontier d N_c) :
    frontier =
      balaban_rg_uniform_lsi_quantitative_frontier_of_rates_frontier d N_c
        frontier.transfer frontier.ratesFrontier := by
  apply Subsingleton.elim

end YangMills.ClayCore
