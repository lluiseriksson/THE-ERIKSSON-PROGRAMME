import Mathlib
import YangMills.ClayCore.BalabanRG.BalabanRGUniformLSILiveTarget

namespace YangMills.ClayCore

/-- Canonical packaged output of the current "last mile":
once the unique live target is discharged, one gets the scale target,
the Haar-LSI target, and the already packaged frontier output. -/
def BalabanRGUniformLSILastMileOutput (d N_c : ℕ) [NeZero N_c] : Prop :=
  SpecialUnitaryScaleLSITarget d N_c ∧
  HaarLSITarget N_c ∧
  HaarLSIFrontierPackage d N_c

/-- Discharging the public Clay-core live target closes the full current last-mile output. -/
theorem balaban_rg_uniform_lsi_last_mile_output_of_live_target
    (d N_c : ℕ) [NeZero N_c]
    (tr : HaarLSIFromUniformLSITransfer N_c)
    (h : BalabanRGUniformLSILiveTarget d N_c) :
    BalabanRGUniformLSILastMileOutput d N_c := by
  refine ⟨?_, ?_, ?_⟩
  · exact scale_lsi_target_of_balaban_rg_uniform_lsi_live_target d N_c h
  · exact haar_lsi_target_of_balaban_rg_uniform_lsi_live_target d N_c tr h
  · exact haar_lsi_frontier_package_of_balaban_rg_uniform_lsi_live_target d N_c tr h

/-- The same packaged output follows from the direct uniform-theorem target. -/
theorem balaban_rg_uniform_lsi_last_mile_output_of_direct_uniform_theorem_target
    (d N_c : ℕ) [NeZero N_c]
    (tr : HaarLSIFromUniformLSITransfer N_c)
    (h : SpecialUnitaryDirectUniformLSITheoremTarget d N_c) :
    BalabanRGUniformLSILastMileOutput d N_c := by
  have h' : BalabanRGUniformLSILiveTarget d N_c := by
    exact (balaban_rg_uniform_lsi_live_target_iff_direct_uniform_theorem_target d N_c).2 h
  exact balaban_rg_uniform_lsi_last_mile_output_of_live_target d N_c tr h'

/-- Projection: the public Clay-core live target already implies the packaged frontier. -/
theorem haar_lsi_frontier_package_of_balaban_rg_uniform_lsi_last_mile
    (d N_c : ℕ) [NeZero N_c]
    (tr : HaarLSIFromUniformLSITransfer N_c)
    (h : BalabanRGUniformLSILiveTarget d N_c) :
    HaarLSIFrontierPackage d N_c := by
  exact (balaban_rg_uniform_lsi_last_mile_output_of_live_target d N_c tr h).2.2

end YangMills.ClayCore
