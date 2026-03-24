import Mathlib
import YangMills.ClayCore.BalabanRG.HaarLSIDirectBridge
import YangMills.ClayCore.BalabanRG.HaarLSIScaleBridge

namespace YangMills.ClayCore

/-- Canonical frontier statement: an actual RG package plus a transfer from uniform LSI to
Haar LSI closes the Haar target. -/
theorem haar_lsi_frontier_of_pkg
    (d N_c : ℕ) [NeZero N_c]
    (tr : HaarLSIFromUniformLSITransfer N_c)
    (pkg : BalabanRGPackage d N_c) :
    HaarLSITarget N_c := by
  exact haar_lsi_from_direct_uniform_theorem d N_c tr
    (direct_uniform_theorem_target_of_pkg pkg)

/-- Same frontier, but through the direct theorem target abstraction. -/
theorem haar_lsi_frontier_of_direct_target
    (d N_c : ℕ) [NeZero N_c]
    (tr : HaarLSIFromUniformLSITransfer N_c)
    (h : SpecialUnitaryDirectUniformLSITheoremTarget d N_c) :
    HaarLSITarget N_c := by
  exact haar_lsi_from_direct_uniform_theorem d N_c tr h

/-- The package also exports a scale-level LSI target. -/
theorem scale_lsi_frontier_of_pkg
    {d N_c : ℕ} [NeZero N_c]
    (pkg : BalabanRGPackage d N_c) :
    SpecialUnitaryScaleLSITarget d N_c := by
  exact scale_lsi_target_of_pkg pkg

/-- Canonical packaged frontier output for the current Haar-LSI lane. -/
def HaarLSIFrontierPackage (d N_c : ℕ) [NeZero N_c] : Prop :=
  SpecialUnitaryScaleLSITarget d N_c ∧ HaarLSITarget N_c

/-- Actual RG package + transfer produce the current packaged frontier output. -/
theorem haar_lsi_frontier_package_of_pkg
    (d N_c : ℕ) [NeZero N_c]
    (tr : HaarLSIFromUniformLSITransfer N_c)
    (pkg : BalabanRGPackage d N_c) :
    HaarLSIFrontierPackage d N_c := by
  refine ⟨?_, ?_⟩
  · exact scale_lsi_target_of_pkg pkg
  · exact haar_lsi_frontier_of_pkg d N_c tr pkg

end YangMills.ClayCore
