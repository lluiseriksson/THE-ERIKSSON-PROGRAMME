import Mathlib
import YangMills.ClayCore.BalabanRG.BalabanRGUniformLSIEquivalenceRegistry

namespace YangMills.ClayCore

/-- Canonical public front-end for the current Balaban-RG / Haar-LSI lane:
it packages both the equivalence registry for the live hypotheses and the
structured closure package exported by the current frontier. -/
structure BalabanRGUniformLSIPublicFacade (d N_c : ℕ) [NeZero N_c] : Prop where
  registry : BalabanRGUniformLSIEquivalenceRegistry d N_c
  closure : BalabanRGUniformLSIClosurePackage d N_c

/-- Preferred public facade from the preferred public live target. -/
theorem balaban_rg_uniform_lsi_public_facade_of_live_target
    (d N_c : ℕ) [NeZero N_c]
    (tr : HaarLSIFromUniformLSITransfer N_c)
    (h : BalabanRGUniformLSILiveTarget d N_c) :
    BalabanRGUniformLSIPublicFacade d N_c := by
  refine ⟨?_, ?_⟩
  · exact balaban_rg_uniform_lsi_equivalence_registry d N_c
  · exact balaban_rg_uniform_lsi_closure_package_of_live_target d N_c tr h

/-- Preferred public facade from the direct uniform-theorem target. -/
theorem balaban_rg_uniform_lsi_public_facade_of_direct_uniform_theorem_target
    (d N_c : ℕ) [NeZero N_c]
    (tr : HaarLSIFromUniformLSITransfer N_c)
    (h : SpecialUnitaryDirectUniformLSITheoremTarget d N_c) :
    BalabanRGUniformLSIPublicFacade d N_c := by
  refine ⟨?_, ?_⟩
  · exact balaban_rg_uniform_lsi_equivalence_registry d N_c
  · exact balaban_rg_uniform_lsi_closure_package_of_direct_uniform_theorem_target d N_c tr h

/-- Preferred public facade from the old conditional target name. -/
theorem balaban_rg_uniform_lsi_public_facade_of_conditional_target
    (d N_c : ℕ) [NeZero N_c]
    (tr : HaarLSIFromUniformLSITransfer N_c)
    (h : BalabanRGUniformLSIConditionalTarget d N_c) :
    BalabanRGUniformLSIPublicFacade d N_c := by
  refine ⟨?_, ?_⟩
  · exact balaban_rg_uniform_lsi_equivalence_registry d N_c
  · exact balaban_rg_uniform_lsi_closure_package_of_conditional_target d N_c tr h

/-- Preferred public facade from the old Haar-lane live target name. -/
theorem balaban_rg_uniform_lsi_public_facade_of_haar_lsi_live_target
    (d N_c : ℕ) [NeZero N_c]
    (tr : HaarLSIFromUniformLSITransfer N_c)
    (h : HaarLSILiveTarget d N_c) :
    BalabanRGUniformLSIPublicFacade d N_c := by
  refine ⟨?_, ?_⟩
  · exact balaban_rg_uniform_lsi_equivalence_registry d N_c
  · exact balaban_rg_uniform_lsi_closure_package_of_haar_lsi_live_target d N_c tr h

/-- Preferred public facade from an actual Balaban-RG package witness. -/
theorem balaban_rg_uniform_lsi_public_facade_of_pkg
    (d N_c : ℕ) [NeZero N_c]
    (tr : HaarLSIFromUniformLSITransfer N_c)
    (pkg : BalabanRGPackage d N_c) :
    BalabanRGUniformLSIPublicFacade d N_c := by
  refine ⟨?_, ?_⟩
  · exact balaban_rg_uniform_lsi_equivalence_registry d N_c
  · exact balaban_rg_uniform_lsi_closure_package_of_pkg d N_c tr pkg

/-- Preferred public facade from the bare package-witness form. -/
theorem balaban_rg_uniform_lsi_public_facade_of_pkg_witness
    (d N_c : ℕ) [NeZero N_c]
    (tr : HaarLSIFromUniformLSITransfer N_c)
    (h : ∃ pkg : BalabanRGPackage d N_c, True) :
    BalabanRGUniformLSIPublicFacade d N_c := by
  refine ⟨?_, ?_⟩
  · exact balaban_rg_uniform_lsi_equivalence_registry d N_c
  · exact balaban_rg_uniform_lsi_closure_package_of_pkg_witness d N_c tr h

/-- Projection to the preferred structured closure package. -/
theorem closure_package_of_balaban_rg_uniform_lsi_public_facade
    {d N_c : ℕ} [NeZero N_c]
    (facade : BalabanRGUniformLSIPublicFacade d N_c) :
    BalabanRGUniformLSIClosurePackage d N_c := by
  exact facade.closure

/-- Projection to the public equivalence registry. -/
theorem equivalence_registry_of_balaban_rg_uniform_lsi_public_facade
    {d N_c : ℕ} [NeZero N_c]
    (facade : BalabanRGUniformLSIPublicFacade d N_c) :
    BalabanRGUniformLSIEquivalenceRegistry d N_c := by
  exact facade.registry

/-- Projection to the scale target through the preferred public facade. -/
theorem scale_target_of_balaban_rg_uniform_lsi_public_facade
    {d N_c : ℕ} [NeZero N_c]
    (facade : BalabanRGUniformLSIPublicFacade d N_c) :
    SpecialUnitaryScaleLSITarget d N_c := by
  exact facade.closure.scaleTarget

/-- Projection to the Haar target through the preferred public facade. -/
theorem haar_target_of_balaban_rg_uniform_lsi_public_facade
    {d N_c : ℕ} [NeZero N_c]
    (facade : BalabanRGUniformLSIPublicFacade d N_c) :
    HaarLSITarget N_c := by
  exact facade.closure.haarTarget

/-- Projection to the frontier package through the preferred public facade. -/
theorem frontier_package_of_balaban_rg_uniform_lsi_public_facade
    {d N_c : ℕ} [NeZero N_c]
    (facade : BalabanRGUniformLSIPublicFacade d N_c) :
    HaarLSIFrontierPackage d N_c := by
  exact facade.closure.frontierPackage

end YangMills.ClayCore
