import Mathlib
import YangMills.ClayCore.BalabanRG.HaarLSIFrontier

namespace YangMills.ClayCore

/-- Canonical remaining live target for the present Haar-LSI lane:
one still needs an actual Balaban RG package giving the uniform-LSI content. -/
def BalabanRGUniformLSIConditionalTarget (d N_c : ℕ) [NeZero N_c] : Prop :=
  ∃ pkg : BalabanRGPackage d N_c, True

/-- The remaining live target is exactly package existence. -/
theorem balaban_rg_uniform_lsi_conditional_target_of_pkg
    {d N_c : ℕ} [NeZero N_c]
    (pkg : BalabanRGPackage d N_c) :
    BalabanRGUniformLSIConditionalTarget d N_c := by
  exact ⟨pkg, trivial⟩

/-- Once the live package target is discharged, the current Haar-LSI frontier closes. -/
theorem haar_lsi_frontier_package_of_conditional_target
    (d N_c : ℕ) [NeZero N_c]
    (tr : HaarLSIFromUniformLSITransfer N_c)
    (h : BalabanRGUniformLSIConditionalTarget d N_c) :
    HaarLSIFrontierPackage d N_c := by
  rcases h with ⟨pkg, _⟩
  exact haar_lsi_frontier_package_of_pkg d N_c tr pkg

/-- Same consequence at the bare Haar-LSI target level. -/
theorem haar_lsi_target_of_conditional_target
    (d N_c : ℕ) [NeZero N_c]
    (tr : HaarLSIFromUniformLSITransfer N_c)
    (h : BalabanRGUniformLSIConditionalTarget d N_c) :
    HaarLSITarget N_c := by
  exact (haar_lsi_frontier_package_of_conditional_target d N_c tr h).2

/-- Same consequence at the scale-level target. -/
theorem scale_lsi_target_of_conditional_target
    (d N_c : ℕ) [NeZero N_c]
    (h : BalabanRGUniformLSIConditionalTarget d N_c) :
    SpecialUnitaryScaleLSITarget d N_c := by
  rcases h with ⟨pkg, _⟩
  exact scale_lsi_frontier_of_pkg pkg

end YangMills.ClayCore
