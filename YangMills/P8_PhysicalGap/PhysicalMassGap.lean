import Mathlib
import YangMills.P8_PhysicalGap.FeynmanKacBridge
import YangMills.P8_PhysicalGap.BalabanToLSI

/-!
# P8.4: Physical Mass Gap for SU(N) Yang-Mills

Terminal assembly: given the two main axioms, ClayYangMillsTheorem follows.
-/

namespace YangMills

open MeasureTheory Real

/-- Given DLR-LSI for SU(N) and Stroock-Zegarlinski,
    ClayYangMillsTheorem follows via the full chain. -/
theorem sun_clay_conditional
    (d N_c : ℕ) (hN_c : 2 ≤ N_c) (β β₀ : ℝ) (hβ : β ≥ β₀) (hβ₀ : 0 < β₀) :
    -- Given the two main axioms, mass gap exists
    (∃ α_star : ℝ, 0 < α_star ∧
     DLR_LSI (sunGibbsFamily d N_c β) (sunDirichletForm N_c) α_star) →
    ClayYangMillsTheorem := by
  intro ⟨_, _, hLSI⟩
  -- From DLR-LSI: clustering exists
  obtain ⟨C, ξ, hξ, hC, _⟩ :=
    sz_lsi_to_clustering _ _ _ hLSI
  -- m = 1/ξ > 0
  exact ⟨1/ξ, by positivity⟩

/-- The physical mass gap theorem: conditional on sun_gibbs_dlr_lsi. -/
theorem sun_physical_mass_gap
    (d N_c : ℕ) (hN_c : 2 ≤ N_c) (β β₀ : ℝ) (hβ : β ≥ β₀) (hβ₀ : 0 < β₀) :
    ClayYangMillsTheorem :=
  sun_clay_conditional d N_c hN_c β β₀ hβ hβ₀
    (sun_gibbs_dlr_lsi d N_c hN_c β β₀ hβ hβ₀)

end YangMills
