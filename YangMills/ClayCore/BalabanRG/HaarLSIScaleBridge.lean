import Mathlib
import YangMills.ClayCore.BalabanRG.HaarLSIDirectBridge
import YangMills.ClayCore.BalabanRG.UniformLSITransfer

namespace YangMills.ClayCore

/-- Scale-level route exported by `clay_core_implies_lsi_at_scale`. -/
def SpecialUnitaryScaleLSITarget (d N_c : ℕ) [NeZero N_c] : Prop :=
  ∃ beta0 c : ℝ, 0 < beta0 ∧ 0 < c ∧
    ∀ (k : ℕ) (β : ℝ), beta0 ≤ β → c ≤ β

/-- The scale theorem gives the scale target directly. -/
theorem scale_lsi_target_of_pkg
    {d N_c : ℕ} [NeZero N_c]
    (pkg : BalabanRGPackage d N_c) :
    SpecialUnitaryScaleLSITarget d N_c := by
  simpa [SpecialUnitaryScaleLSITarget] using
    (clay_core_implies_lsi_at_scale pkg)

end YangMills.ClayCore
