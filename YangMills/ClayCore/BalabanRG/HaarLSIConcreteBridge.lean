import Mathlib
import YangMills.ClayCore.BalabanRG.HaarLSIBridge
import YangMills.ClayCore.BalabanRG.HaarLSIDirectBridge

namespace YangMills.ClayCore

/-- Legacy compatibility name for the concrete package-level target. It is now exactly the
direct package theorem target. -/
def SpecialUnitaryConcreteUniformLSITarget (d N_c : ℕ) [NeZero N_c] : Prop :=
  SpecialUnitaryDirectUniformLSITheoremTarget d N_c

/-- The legacy concrete target is definitionally the current direct theorem target. -/
theorem concrete_uniform_target_iff_direct_uniform_theorem_target
    (d N_c : ℕ) [NeZero N_c] :
    SpecialUnitaryConcreteUniformLSITarget d N_c ↔
      SpecialUnitaryDirectUniformLSITheoremTarget d N_c := by
  rfl

/-- Any actual package still discharges the old concrete target name. -/
theorem concrete_uniform_target_of_pkg
    {d N_c : ℕ} [NeZero N_c]
    (pkg : BalabanRGPackage d N_c) :
    SpecialUnitaryConcreteUniformLSITarget d N_c := by
  exact direct_uniform_theorem_target_of_pkg pkg

/-- The old concrete target name still implies the abstract uniform-LSI package target,
but now through the direct theorem route. -/
theorem abstract_uniform_target_of_concrete_uniform_lsi
    {d N_c : ℕ} [NeZero N_c]
    (h : SpecialUnitaryConcreteUniformLSITarget d N_c) :
    SpecialUnitaryUniformLSIPackageTarget N_c := by
  exact abstract_uniform_target_of_direct_theorem h

/-- Legacy compatibility theorem: old concrete target name to Haar-LSI target.
The proof payload is now the direct abstract route. -/
theorem haar_lsi_target_of_concrete_uniform_lsi
    (d N_c : ℕ) [NeZero N_c]
    (tr : HaarLSIFromUniformLSITransfer N_c)
    (h : SpecialUnitaryConcreteUniformLSITarget d N_c) :
    HaarLSITarget N_c := by
  exact haar_lsi_from_direct_uniform_theorem d N_c tr h

end YangMills.ClayCore
