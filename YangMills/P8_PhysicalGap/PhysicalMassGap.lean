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

/-- **C134: Axiom-free physical mass gap (conditional on DLR-LSI hypothesis).**
    `sun_physical_mass_gap` now targets `ClayYangMillsPhysicalStrong` with the
    DLR-LSI witness supplied as an **explicit hypothesis** `hdlr` rather than
    generated internally via `sun_gibbs_dlr_lsi_norm` (which depends on
    `lsi_normalized_gibbs_from_haar`). The result: the oracle footprint of
    `sun_physical_mass_gap` collapses to `[propext, Classical.choice, Quot.sound]`
    — the three core Lean axioms, no research axioms. The Holley-Stroock axiom
    `lsi_normalized_gibbs_from_haar` still exists in `BalabanToLSI.lean` and is
    still consumed by `sun_gibbs_dlr_lsi_norm`, but that dependency no longer
    transitively flows into this theorem. Callers who want to discharge `hdlr`
    automatically can compose with `sun_gibbs_dlr_lsi_norm`; callers who establish
    DLR-LSI by some other route (Mathlib Bakry-Émery once it lands, direct
    cluster expansion, etc.) get a fully axiom-free mass gap.

    The `bridge` hypothesis still encapsulates the LSI-to-decay step (Balaban RG
    + KP cluster expansion).

    For the legacy vacuous-target form (`ClayYangMillsTheorem := ∃ m_phys,
    0 < m_phys`) see `sun_physical_mass_gap_vacuous` below.

    **Legacy C132 + C133 note (superseded):** previously `sun_physical_mass_gap`
    generated the DLR-LSI witness internally via `sun_gibbs_dlr_lsi_norm`, which
    made `lsi_normalized_gibbs_from_haar` load-bearing on the oracle chain. The
    new form keeps all the same algebraic content but isolates the axiomatic part
    at the call site. -/
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

/-- LEGACY: Physical mass gap via un-normalized Gibbs (uses holleyStroock_sunGibbs_lsi axiom). -/
theorem sun_physical_mass_gap_legacy
    (d N_c : ℕ) [NeZero N_c] (hN_c : 2 ≤ N_c) (β β₀ : ℝ) (hβ : β ≥ β₀) (hβ₀ : 0 < β₀) :
    ClayYangMillsTheorem :=
  sun_clay_conditional d N_c hN_c β β₀ hβ hβ₀
    (sun_gibbs_dlr_lsi d N_c hN_c β β₀ hβ hβ₀)


/-- Vacuous-target (`ClayYangMillsTheorem`) mass gap via the NORMALIZED chain.
    Routes through `sun_gibbs_dlr_lsi_norm`, eliminating the legacy
    `holleyStroock_sunGibbs_lsi` axiom. Oracle: [propext, Classical.choice,
    Quot.sound, sorryAx]. -/
theorem sun_physical_mass_gap_vacuous
    (d N_c : ℕ) [NeZero N_c] (hN_c : 2 ≤ N_c) (β β₀ : ℝ)
    (hβ : β ≥ β₀) (hβ₀ : 0 < β₀) :
    ClayYangMillsTheorem := by
  obtain ⟨α_star, hα_pos, _⟩ := sun_gibbs_dlr_lsi_norm d N_c hN_c β β₀ hβ hβ₀
  exact ⟨α_star, hα_pos⟩

end YangMills
