import Mathlib
import YangMills.ClayCore.BalabanRG.BalabanRGUniformLSIClosurePackage

namespace YangMills.ClayCore

/-- Any actual Balaban-RG package witness immediately discharges the public live target. -/
theorem balaban_rg_uniform_lsi_live_target_of_pkg
    {d N_c : ℕ} [NeZero N_c]
    (pkg : BalabanRGPackage d N_c) :
    BalabanRGUniformLSILiveTarget d N_c := by
  exact
    (balaban_rg_uniform_lsi_live_target_iff_direct_uniform_theorem_target d N_c).2
      (direct_uniform_theorem_target_of_pkg pkg)

/-- Any actual Balaban-RG package witness already yields the bundled last-mile output. -/
theorem balaban_rg_uniform_lsi_last_mile_output_of_pkg
    (d N_c : ℕ) [NeZero N_c]
    (tr : HaarLSIFromUniformLSITransfer N_c)
    (pkg : BalabanRGPackage d N_c) :
    BalabanRGUniformLSILastMileOutput d N_c := by
  exact
    balaban_rg_uniform_lsi_last_mile_output_of_live_target d N_c tr
      (balaban_rg_uniform_lsi_live_target_of_pkg pkg)

/-- Any actual Balaban-RG package witness yields the canonical public closure package. -/
theorem balaban_rg_uniform_lsi_closure_package_of_pkg
    (d N_c : ℕ) [NeZero N_c]
    (tr : HaarLSIFromUniformLSITransfer N_c)
    (pkg : BalabanRGPackage d N_c) :
    BalabanRGUniformLSIClosurePackage d N_c := by
  exact
    balaban_rg_uniform_lsi_closure_package_of_live_target d N_c tr
      (balaban_rg_uniform_lsi_live_target_of_pkg pkg)

/-- Projection: a package witness already yields the scale target. -/
theorem scale_target_of_balaban_rg_uniform_lsi_pkg
    {d N_c : ℕ} [NeZero N_c]
    (pkg : BalabanRGPackage d N_c) :
    SpecialUnitaryScaleLSITarget d N_c := by
  exact
    scale_lsi_target_of_balaban_rg_uniform_lsi_live_target d N_c
      (balaban_rg_uniform_lsi_live_target_of_pkg pkg)

/-- Projection: a package witness plus transfer already yields the Haar target. -/
theorem haar_target_of_balaban_rg_uniform_lsi_pkg
    (d N_c : ℕ) [NeZero N_c]
    (tr : HaarLSIFromUniformLSITransfer N_c)
    (pkg : BalabanRGPackage d N_c) :
    HaarLSITarget N_c := by
  exact
    (balaban_rg_uniform_lsi_closure_package_of_pkg d N_c tr pkg).haarTarget

/-- Projection: a package witness plus transfer already yields the frontier package. -/
theorem frontier_package_of_balaban_rg_uniform_lsi_pkg
    (d N_c : ℕ) [NeZero N_c]
    (tr : HaarLSIFromUniformLSITransfer N_c)
    (pkg : BalabanRGPackage d N_c) :
    HaarLSIFrontierPackage d N_c := by
  exact
    (balaban_rg_uniform_lsi_closure_package_of_pkg d N_c tr pkg).frontierPackage

end YangMills.ClayCore
