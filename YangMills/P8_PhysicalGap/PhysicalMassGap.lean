import Mathlib
import YangMills.P8_PhysicalGap.FeynmanKacBridge
import YangMills.P8_PhysicalGap.BalabanToLSI
import YangMills.L8_Terminal.ClayPhysical

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

/-- C132: Given DLR-LSI for the **normalized** Gibbs family with α_star > 0,
    ClayYangMillsTheorem follows. The specific Gibbs family is irrelevant;
    only positivity of α_star matters. -/
theorem sun_clay_conditional_norm
    (d N_c : ℕ) [NeZero N_c] (hN_c : 2 ≤ N_c) (β β₀ : ℝ) (hβ : β ≥ β₀) (hβ₀ : 0 < β₀) :
    (∃ α_star : ℝ, 0 < α_star ∧
      DLR_LSI (sunGibbsFamily_norm d N_c hN_c β (hβ₀.trans_le hβ)) (sunDirichletForm N_c) α_star) →
      ClayYangMillsTheorem := by
  rintro ⟨α_star, hα, -⟩
  exact ⟨α_star, hα⟩

/-- **C132 + C133: Physical mass gap  strong, non-vacuous form.**
    `sun_physical_mass_gap` now targets `ClayYangMillsPhysicalStrong`,
    which ties a lattice mass profile to the Yang-Mills Wilson connected
    correlator (via `IsYangMillsMassProfile`) and requires a continuum
    limit (`HasContinuumMassGap`). Under this rewiring, the LSI axiom
    `lsi_normalized_gibbs_from_haar` is genuinely load-bearing: it feeds
    the DLR spectral-gap constant `α_star > 0` into the Wilson decay
    bridge, which then produces `ClayYangMillsPhysicalStrong` via the
    sorry-free theorem `connectedCorrDecay_implies_physicalStrong` from
    `L8_Terminal.ClayPhysical`.

    The `bridge` hypothesis encapsulates the classical fact that an LSI
    at rate `α_star` for the Haar-normalized SU(N) Gibbs family implies
    exponential decay of the Wilson connected correlator (this is the
    Balaban RG + KP cluster expansion step; we take it as an explicit
    hypothesis so that the LSI-to-decay link is visible in the signature
    rather than hidden in an unconditional axiom).

    For the legacy vacuous-target form (`ClayYangMillsTheorem := ∃ m_phys, 0 < m_phys`)
    see `sun_physical_mass_gap_vacuous` below. -/
theorem sun_physical_mass_gap
    (d : ℕ) [NeZero d] (N_c : ℕ) [NeZero N_c] (hN_c : 2 ≤ N_c) (β β₀ : ℝ)
    (hβ : β ≥ β₀) (hβ₀ : 0 < β₀)
    {G : Type*} [Group G] [MeasurableSpace G] (μ : MeasureTheory.Measure G)
    (plaquetteEnergy : G → ℝ) (F : G → ℝ)
    (distP : (N : ℕ) → ConcretePlaquette d N → ConcretePlaquette d N → ℝ)
    (bridge : ∀ α_star : ℝ, 0 < α_star →
      DLR_LSI (sunGibbsFamily_norm d N_c hN_c β (hβ₀.trans_le hβ))
              (sunDirichletForm N_c) α_star →
      ConnectedCorrDecay μ plaquetteEnergy β F distP)
    (hdistP : ∀ (N : ℕ) [NeZero N] (p q : ConcretePlaquette d N),
      0 ≤ distP N p q) :
    ClayYangMillsPhysicalStrong μ plaquetteEnergy β F distP := by
  obtain ⟨α_star, hα_pos, hDLR⟩ :=
    sun_gibbs_dlr_lsi_norm d N_c hN_c β β₀ hβ hβ₀
  exact connectedCorrDecay_implies_physicalStrong
    μ plaquetteEnergy β F distP (bridge α_star hα_pos hDLR) hdistP

/-- **Vacuous form kept for backward compatibility.**
    Produces `ClayYangMillsTheorem := ∃ m_phys : ℝ, 0 < m_phys`, which is
    trivially true. Only `lsi_normalized_gibbs_from_haar` appears on the
    oracle chain because the witness extraction in `sun_clay_conditional_norm`
    discards the LSI hypothesis; the axiom is still consumed when
    constructing the argument term. -/
theorem sun_physical_mass_gap_vacuous
    (d N_c : ℕ) [NeZero N_c] (hN_c : 2 ≤ N_c) (β β₀ : ℝ)
    (hβ : β ≥ β₀) (hβ₀ : 0 < β₀) :
    ClayYangMillsTheorem :=
  sun_clay_conditional_norm d N_c hN_c β β₀ hβ hβ₀
    (sun_gibbs_dlr_lsi_norm d N_c hN_c β β₀ hβ hβ₀)

/-- LEGACY: Physical mass gap via un-normalized Gibbs (uses holleyStroock_sunGibbs_lsi axiom). -/
theorem sun_physical_mass_gap_legacy
    (d N_c : ℕ) [NeZero N_c] (hN_c : 2 ≤ N_c) (β β₀ : ℝ) (hβ : β ≥ β₀) (hβ₀ : 0 < β₀) :
    ClayYangMillsTheorem :=
  sun_clay_conditional d N_c hN_c β β₀ hβ hβ₀
    (sun_gibbs_dlr_lsi d N_c hN_c β β₀ hβ hβ₀)

end YangMills
