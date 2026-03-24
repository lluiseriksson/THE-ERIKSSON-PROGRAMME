import Mathlib
import YangMills.ClayCore.BalabanRG.HaarLSIBridge
import YangMills.ClayCore.BalabanRG.UniformLSITransfer

namespace YangMills.ClayCore

/-- Direct route target: an actual RG package is available. -/
def SpecialUnitaryDirectUniformLSITheoremTarget (d N_c : ℕ) [NeZero N_c] : Prop :=
  ∃ pkg : BalabanRGPackage d N_c, True

/-- The direct package route already implies the abstract uniform-LSI package target used
by the Haar bridge. No concrete bridge is needed here. -/
theorem abstract_uniform_target_of_direct_theorem
    {d N_c : ℕ} [NeZero N_c]
    (h : SpecialUnitaryDirectUniformLSITheoremTarget d N_c) :
    SpecialUnitaryUniformLSIPackageTarget N_c := by
  rcases h with ⟨pkg, _⟩
  obtain ⟨c, hc, _hlsi⟩ := uniform_lsi_of_balaban_rg_package pkg
  exact ⟨c, hc⟩

/-- Any package gives the direct theorem target. -/
theorem direct_uniform_theorem_target_of_pkg
    {d N_c : ℕ} [NeZero N_c]
    (pkg : BalabanRGPackage d N_c) :
    SpecialUnitaryDirectUniformLSITheoremTarget d N_c := by
  exact ⟨pkg, trivial⟩

/-- Direct package route to Haar-LSI through the abstract bridge only. -/
theorem haar_lsi_from_direct_uniform_theorem
    (d N_c : ℕ) [NeZero N_c]
    (tr : HaarLSIFromUniformLSITransfer N_c)
    (h : SpecialUnitaryDirectUniformLSITheoremTarget d N_c) :
    HaarLSITarget N_c := by
  exact haar_lsi_target_of_uniform_lsi N_c tr (abstract_uniform_target_of_direct_theorem h)

end YangMills.ClayCore
