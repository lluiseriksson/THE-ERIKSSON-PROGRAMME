import YangMills.ClayCore.BalabanRG.HaarLSIBridge
import YangMills.ClayCore.BalabanRG.UniformLSITransfer

namespace YangMills
namespace ClayCore

noncomputable section

/-- Direct theorem-side target used by the Haar-LSI direct bridge. -/
def SpecialUnitaryDirectUniformLSITheoremTarget
    (d N_c : ℕ) [NeZero N_c] : Prop :=
  ∃ pkg : BalabanRGPackage d N_c, True

/-- Actual Balaban-RG package -> direct theorem-side target. -/
theorem direct_uniform_target_of_pkg
    {d N_c : ℕ} [NeZero N_c]
    (pkg : BalabanRGPackage d N_c) :
    SpecialUnitaryDirectUniformLSITheoremTarget d N_c := by
  exact ⟨pkg, trivial⟩

/-- Legacy alias expected by upper wrappers. -/
theorem direct_uniform_theorem_target_of_pkg
    {d N_c : ℕ} [NeZero N_c]
    (pkg : BalabanRGPackage d N_c) :
    SpecialUnitaryDirectUniformLSITheoremTarget d N_c := by
  exact direct_uniform_target_of_pkg pkg

/-- The direct theorem-side target upgrades to the stronger abstract uniform-LSI target. -/
theorem direct_uniform_lsi_implies_abstract_uniform_target
    {d N_c : ℕ} [NeZero N_c]
    (h : SpecialUnitaryDirectUniformLSITheoremTarget d N_c) :
    SpecialUnitaryUniformLSIPackageTarget N_c := by
  rcases h with ⟨pkg, _⟩
  exact abstract_uniform_target_of_pkg pkg

/-- Legacy alias expected by `HaarLSIConcreteBridge`.
This one uses implicit `d N_c` so callers can just write
`abstract_uniform_target_of_direct_theorem h`. -/
theorem abstract_uniform_target_of_direct_theorem
    {d N_c : ℕ} [NeZero N_c]
    (h : SpecialUnitaryDirectUniformLSITheoremTarget d N_c) :
    SpecialUnitaryUniformLSIPackageTarget N_c := by
  exact direct_uniform_lsi_implies_abstract_uniform_target h

/-- Explicit-form compatibility alias, kept for scripts that pass `d N_c` manually. -/
theorem abstract_uniform_target_of_direct_theorem_explicit
    (d N_c : ℕ) [NeZero N_c]
    (h : SpecialUnitaryDirectUniformLSITheoremTarget d N_c) :
    SpecialUnitaryUniformLSIPackageTarget N_c := by
  exact direct_uniform_lsi_implies_abstract_uniform_target h

/-- Direct elimination toward the strong analytic Haar-LSI target. -/
theorem analytic_haar_lsi_target_of_direct_uniform_lsi
    (d N_c : ℕ) [NeZero N_c]
    (tr : HaarLSIFromUniformLSIAnalyticTransfer N_c)
    (h : SpecialUnitaryDirectUniformLSITheoremTarget d N_c) :
    HaarLSIAnalyticTarget N_c := by
  exact tr (direct_uniform_lsi_implies_abstract_uniform_target h)

/-- Eliminación directa hacia el target Haar-LSI legacy. -/
theorem haar_lsi_target_of_direct_uniform_lsi
    (d N_c : ℕ) [NeZero N_c]
    (tr : HaarLSIFromUniformLSITransfer N_c)
    (h : SpecialUnitaryDirectUniformLSITheoremTarget d N_c) :
    HaarLSITarget N_c := by
  exact
    haar_lsi_target_of_uniform_lsi N_c tr
      (direct_uniform_lsi_implies_abstract_uniform_target h)

/-- Same direct elimination, but through the stronger analytic transfer. -/
theorem haar_lsi_target_of_direct_uniform_lsi_via_analytic
    (d N_c : ℕ) [NeZero N_c]
    (tr : HaarLSIFromUniformLSIAnalyticTransfer N_c)
    (h : SpecialUnitaryDirectUniformLSITheoremTarget d N_c) :
    HaarLSITarget N_c := by
  exact
    haar_lsi_target_of_uniform_lsi_via_analytic N_c tr
      (direct_uniform_lsi_implies_abstract_uniform_target h)

/-- Alias legacy theorem-side esperado por `HaarLSIFrontier`. -/
theorem haar_lsi_from_direct_uniform_theorem
    (d N_c : ℕ) [NeZero N_c]
    (tr : HaarLSIFromUniformLSITransfer N_c)
    (h : SpecialUnitaryDirectUniformLSITheoremTarget d N_c) :
    HaarLSITarget N_c := by
  exact haar_lsi_target_of_direct_uniform_lsi d N_c tr h

/-- Strong analytic alias parallel to the legacy one. -/
theorem analytic_haar_lsi_from_direct_uniform_theorem
    (d N_c : ℕ) [NeZero N_c]
    (tr : HaarLSIFromUniformLSIAnalyticTransfer N_c)
    (h : SpecialUnitaryDirectUniformLSITheoremTarget d N_c) :
    HaarLSIAnalyticTarget N_c := by
  exact analytic_haar_lsi_target_of_direct_uniform_lsi d N_c tr h

/-- Paquete RG -> vista directa -> target abstracto reforzado -> Haar-LSI. -/
theorem haar_lsi_from_direct_via_abstract
    (d N_c : ℕ) [NeZero N_c]
    (tr : HaarLSIFromUniformLSITransfer N_c)
    (pkg : BalabanRGPackage d N_c) :
    HaarLSITarget N_c := by
  exact
    haar_lsi_from_direct_uniform_theorem d N_c tr
      (direct_uniform_target_of_pkg pkg)

/-- Paquete RG -> vista directa -> target analítico fuerte. -/
theorem analytic_haar_lsi_from_direct_via_abstract
    (d N_c : ℕ) [NeZero N_c]
    (tr : HaarLSIFromUniformLSIAnalyticTransfer N_c)
    (pkg : BalabanRGPackage d N_c) :
    HaarLSIAnalyticTarget N_c := by
  exact
    analytic_haar_lsi_from_direct_uniform_theorem d N_c tr
      (direct_uniform_target_of_pkg pkg)

end

end YangMills.ClayCore
