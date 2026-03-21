import Mathlib
import YangMills.ClayCore.BalabanRG.HaarLSILiveTarget

namespace YangMills.ClayCore

/-- Canonical Clay-core public name for the unique remaining live target in the
present Balaban RG / Haar-LSI lane. -/
def BalabanRGUniformLSILiveTarget (d N_c : ℕ) [NeZero N_c] : Prop :=
  HaarLSILiveTarget d N_c

/-- This is definitionally the same live target as `HaarLSILiveTarget`. -/
theorem balaban_rg_uniform_lsi_live_target_iff_haar_lsi_live_target
    (d N_c : ℕ) [NeZero N_c] :
    BalabanRGUniformLSILiveTarget d N_c ↔ HaarLSILiveTarget d N_c := by
  rfl

/-- Equivalently, the public Clay-core live target is the direct uniform-theorem target. -/
theorem balaban_rg_uniform_lsi_live_target_iff_direct_uniform_theorem_target
    (d N_c : ℕ) [NeZero N_c] :
    BalabanRGUniformLSILiveTarget d N_c ↔
      SpecialUnitaryDirectUniformLSITheoremTarget d N_c := by
  exact haar_lsi_live_target_iff_direct_uniform_theorem_target d N_c

/-- Once the live target is solved, the packaged Haar-LSI frontier closes immediately. -/
theorem haar_lsi_frontier_package_of_balaban_rg_uniform_lsi_live_target
    (d N_c : ℕ) [NeZero N_c]
    (tr : HaarLSIFromUniformLSITransfer N_c)
    (h : BalabanRGUniformLSILiveTarget d N_c) :
    HaarLSIFrontierPackage d N_c := by
  exact haar_lsi_frontier_package_of_live_target d N_c tr h

/-- Bare Haar-LSI consequence of the public Clay-core live target. -/
theorem haar_lsi_target_of_balaban_rg_uniform_lsi_live_target
    (d N_c : ℕ) [NeZero N_c]
    (tr : HaarLSIFromUniformLSITransfer N_c)
    (h : BalabanRGUniformLSILiveTarget d N_c) :
    HaarLSITarget N_c := by
  exact haar_lsi_target_of_live_target d N_c tr h

/-- Scale-level consequence of the public Clay-core live target. -/
theorem scale_lsi_target_of_balaban_rg_uniform_lsi_live_target
    (d N_c : ℕ) [NeZero N_c]
    (h : BalabanRGUniformLSILiveTarget d N_c) :
    SpecialUnitaryScaleLSITarget d N_c := by
  exact scale_lsi_target_of_live_target d N_c h

end YangMills.ClayCore
