import Mathlib
import YangMills.ClayCore.BalabanRG.BalabanRGUniformLSILastMile

namespace YangMills.ClayCore

/-- Canonical public closure package for the current Balaban-RG uniform-LSI lane. -/
structure BalabanRGUniformLSIClosurePackage (d N_c : ℕ) [NeZero N_c] : Prop where
  scaleTarget : SpecialUnitaryScaleLSITarget d N_c
  haarTarget : HaarLSITarget N_c
  frontierPackage : HaarLSIFrontierPackage d N_c

/-- The single live-target hypothesis yields the full public closure package. -/
theorem balaban_rg_uniform_lsi_closure_package_of_live_target
    (d N_c : ℕ) [NeZero N_c]
    (tr : HaarLSIFromUniformLSITransfer N_c)
    (h : BalabanRGUniformLSILiveTarget d N_c) :
    BalabanRGUniformLSIClosurePackage d N_c := by
  rcases balaban_rg_uniform_lsi_last_mile_output_of_live_target d N_c tr h with
    ⟨hscale, hhaar, hfrontier⟩
  exact ⟨hscale, hhaar, hfrontier⟩

/-- The direct uniform-theorem target also yields the full public closure package. -/
theorem balaban_rg_uniform_lsi_closure_package_of_direct_uniform_theorem_target
    (d N_c : ℕ) [NeZero N_c]
    (tr : HaarLSIFromUniformLSITransfer N_c)
    (h : SpecialUnitaryDirectUniformLSITheoremTarget d N_c) :
    BalabanRGUniformLSIClosurePackage d N_c := by
  rcases balaban_rg_uniform_lsi_last_mile_output_of_direct_uniform_theorem_target d N_c tr h with
    ⟨hscale, hhaar, hfrontier⟩
  exact ⟨hscale, hhaar, hfrontier⟩

/-- Projection to the scale target. -/
theorem scale_target_of_balaban_rg_uniform_lsi_closure_package
    {d N_c : ℕ} [NeZero N_c]
    (pkg : BalabanRGUniformLSIClosurePackage d N_c) :
    SpecialUnitaryScaleLSITarget d N_c := by
  exact pkg.scaleTarget

/-- Projection to the Haar-LSI target. -/
theorem haar_target_of_balaban_rg_uniform_lsi_closure_package
    {d N_c : ℕ} [NeZero N_c]
    (pkg : BalabanRGUniformLSIClosurePackage d N_c) :
    HaarLSITarget N_c := by
  exact pkg.haarTarget

/-- Projection to the frontier package. -/
theorem frontier_package_of_balaban_rg_uniform_lsi_closure_package
    {d N_c : ℕ} [NeZero N_c]
    (pkg : BalabanRGUniformLSIClosurePackage d N_c) :
    HaarLSIFrontierPackage d N_c := by
  exact pkg.frontierPackage

end YangMills.ClayCore
