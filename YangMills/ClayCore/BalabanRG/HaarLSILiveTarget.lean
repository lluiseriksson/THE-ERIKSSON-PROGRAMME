import Mathlib
import YangMills.ClayCore.BalabanRG.HaarLSIConditionalClosure
import YangMills.ClayCore.BalabanRG.HaarLSIDirectBridge

namespace YangMills.ClayCore

/-- Canonical public name for the unique remaining live target in the current Haar-LSI lane:
it is exactly the direct package theorem target. -/
def HaarLSILiveTarget (d N_c : ℕ) [NeZero N_c] : Prop :=
  SpecialUnitaryDirectUniformLSITheoremTarget d N_c

/-- The live target is definitionally the already existing direct-package theorem target. -/
theorem haar_lsi_live_target_iff_direct_uniform_theorem_target
    (d N_c : ℕ) [NeZero N_c] :
    HaarLSILiveTarget d N_c ↔ SpecialUnitaryDirectUniformLSITheoremTarget d N_c := by
  rfl

/-- Once the live target is solved, the packaged frontier closes immediately. -/
theorem haar_lsi_frontier_package_of_live_target
    (d N_c : ℕ) [NeZero N_c]
    (tr : HaarLSIFromUniformLSITransfer N_c)
    (h : HaarLSILiveTarget d N_c) :
    HaarLSIFrontierPackage d N_c := by
  exact haar_lsi_frontier_package_of_conditional_target d N_c tr h

/-- Bare Haar-LSI consequence of the live target. -/
theorem haar_lsi_target_of_live_target
    (d N_c : ℕ) [NeZero N_c]
    (tr : HaarLSIFromUniformLSITransfer N_c)
    (h : HaarLSILiveTarget d N_c) :
    HaarLSITarget N_c := by
  exact (haar_lsi_frontier_package_of_live_target d N_c tr h).2

/-- Scale-level consequence of the live target. -/
theorem scale_lsi_target_of_live_target
    (d N_c : ℕ) [NeZero N_c]
    (h : HaarLSILiveTarget d N_c) :
    SpecialUnitaryScaleLSITarget d N_c := by
  exact scale_lsi_target_of_conditional_target d N_c h

end YangMills.ClayCore
