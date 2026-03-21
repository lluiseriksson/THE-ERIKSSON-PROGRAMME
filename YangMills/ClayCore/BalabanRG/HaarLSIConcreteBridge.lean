import Mathlib
import YangMills.ClayCore.BalabanRG.HaarLSIBridge
import YangMills.ClayCore.BalabanRG.UniformLSITransfer

namespace YangMills.ClayCore

/-- Concrete uniform-LSI target extracted from the actual RG theorem. -/
def SpecialUnitaryConcreteUniformLSITarget (d N_c : ℕ) [NeZero N_c] : Prop :=
  ∃ c : ℝ, 0 < c ∧ ClayCoreLSI d N_c c

/-- A real RG package yields the concrete uniform-LSI target. -/
theorem concrete_uniform_target_of_pkg
    {d N_c : ℕ} [NeZero N_c]
    (pkg : BalabanRGPackage d N_c) :
    SpecialUnitaryConcreteUniformLSITarget d N_c := by
  simpa [SpecialUnitaryConcreteUniformLSITarget] using
    (uniform_lsi_of_balaban_rg_package pkg)

/-- Forget the concrete `ClayCoreLSI` witness and keep only positivity,
which is exactly the abstract target used by the Haar bridge. -/
theorem concrete_uniform_lsi_implies_abstract_uniform_target
    {d N_c : ℕ} [NeZero N_c]
    (h : SpecialUnitaryConcreteUniformLSITarget d N_c) :
    SpecialUnitaryUniformLSIPackageTarget N_c := by
  rcases h with ⟨c, hc, _hlsi⟩
  exact ⟨c, hc⟩

/-- Concrete uniform-LSI data closes the Haar-LSI target via the abstract bridge. -/
theorem haar_lsi_target_of_concrete_uniform_lsi
    (d N_c : ℕ) [NeZero N_c]
    (tr : HaarLSIFromUniformLSITransfer N_c)
    (h : SpecialUnitaryConcreteUniformLSITarget d N_c) :
    HaarLSITarget N_c := by
  exact haar_lsi_target_of_uniform_lsi N_c tr
    (concrete_uniform_lsi_implies_abstract_uniform_target h)

/-- Package -> concrete target -> abstract target -> Haar-LSI. -/
theorem haar_lsi_from_concrete_via_abstract
    (d N_c : ℕ) [NeZero N_c]
    (tr : HaarLSIFromUniformLSITransfer N_c)
    (pkg : BalabanRGPackage d N_c) :
    HaarLSITarget N_c := by
  exact haar_lsi_target_of_concrete_uniform_lsi d N_c tr
    (concrete_uniform_target_of_pkg pkg)

end YangMills.ClayCore
