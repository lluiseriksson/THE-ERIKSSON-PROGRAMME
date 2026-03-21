import Mathlib
import YangMills.ClayCore.BalabanRG.HaarLSIConcreteBridge
import YangMills.ClayCore.BalabanRG.UniformLSITransfer

namespace YangMills.ClayCore

/-- Direct route target: an actual RG package is available. -/
def SpecialUnitaryDirectUniformLSITheoremTarget (d N_c : ℕ) [NeZero N_c] : Prop :=
  ∃ pkg : BalabanRGPackage d N_c, True

/-- The direct package route implies the concrete uniform-LSI target. -/
theorem concrete_uniform_target_of_direct_theorem
    {d N_c : ℕ} [NeZero N_c]
    (h : SpecialUnitaryDirectUniformLSITheoremTarget d N_c) :
    SpecialUnitaryConcreteUniformLSITarget d N_c := by
  rcases h with ⟨pkg, _⟩
  exact concrete_uniform_target_of_pkg pkg

/-- Any package gives the direct theorem target. -/
theorem direct_uniform_theorem_target_of_pkg
    {d N_c : ℕ} [NeZero N_c]
    (pkg : BalabanRGPackage d N_c) :
    SpecialUnitaryDirectUniformLSITheoremTarget d N_c := by
  exact ⟨pkg, trivial⟩

/-- Direct package route to Haar-LSI through the concrete bridge. -/
theorem haar_lsi_from_direct_uniform_theorem
    (d N_c : ℕ) [NeZero N_c]
    (tr : HaarLSIFromUniformLSITransfer N_c)
    (h : SpecialUnitaryDirectUniformLSITheoremTarget d N_c) :
    HaarLSITarget N_c := by
  exact haar_lsi_target_of_concrete_uniform_lsi d N_c tr
    (concrete_uniform_target_of_direct_theorem h)

end YangMills.ClayCore
