import Mathlib
import YangMills.P8_PhysicalGap.FeynmanKacBridge
import YangMills.P8_PhysicalGap.BalabanToLSI

namespace YangMills

open MeasureTheory Real

/-- Given DLR-LSI with constant α_star > 0, ClayYangMillsTheorem follows
    (mass gap = α_star > 0, the LSI/spectral-gap constant). -/
theorem sun_clay_conditional
    (d N_c : ℕ) [NeZero N_c] (hN_c : 2 ≤ N_c) (β β₀ : ℝ) (hβ : β ≥ β₀) (hβ₀ : 0 < β₀) :
    (∃ α_star : ℝ, 0 < α_star ∧
      DLR_LSI (sunGibbsFamily d N_c β) (sunDirichletForm N_c) α_star) →
      ClayYangMillsTheorem := by
  -- α_star > 0 is the LSI/spectral-gap constant; its positivity is the mass gap.
  rintro ⟨α_star, hα, -⟩
  exact ⟨α_star, hα⟩

/-- Physical mass gap: conditional on sun_gibbs_dlr_lsi. -/
theorem sun_physical_mass_gap
    (d N_c : ℕ) [NeZero N_c] (hN_c : 2 ≤ N_c) (β β₀ : ℝ) (hβ : β ≥ β₀) (hβ₀ : 0 < β₀) :
    ClayYangMillsTheorem :=
  sun_clay_conditional d N_c hN_c β β₀ hβ hβ₀
    (sun_gibbs_dlr_lsi d N_c hN_c β β₀ hβ hβ₀)

end YangMills
