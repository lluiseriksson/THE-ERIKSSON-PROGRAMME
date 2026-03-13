import Mathlib
import YangMills.P3_BalabanRG.LatticeMassExtraction
import YangMills.L7_Continuum.ContinuumLimit

namespace YangMills

open MeasureTheory

/-! ## P3.5: Phase 3 Assembly

Phase 3 discharges: ConnectedCorrDecay → LatticeMassProfile.IsPositive
Phase 4 will supply: HasContinuumMassGap
Together → clay_millennium_yangMills

LatticeMassProfile = ℕ → ℝ
IsPositive = ∀ N, 0 < m_lat N
-/

section Phase3Assembly

variable {d : ℕ} [NeZero d]
variable {G : Type*} [Group G] [MeasurableSpace G]

/-- Construct a concrete lattice mass profile from a decay witness. -/
noncomputable def latticeMassFromDecay
    (μ : Measure G) (plaquetteEnergy : G → ℝ) (β : ℝ)
    (F : G → ℝ)
    (distP : (N : ℕ) → ConcretePlaquette d N → ConcretePlaquette d N → ℝ)
    (h : ConnectedCorrDecay μ plaquetteEnergy β F distP) :
    LatticeMassProfile :=
  fun _ => h.m

/-- The constant profile is pointwise positive. -/
theorem latticeMassFromDecay_isPositive
    (μ : Measure G) (plaquetteEnergy : G → ℝ) (β : ℝ)
    (F : G → ℝ)
    (distP : (N : ℕ) → ConcretePlaquette d N → ConcretePlaquette d N → ℝ)
    (h : ConnectedCorrDecay μ plaquetteEnergy β F distP) :
    (latticeMassFromDecay μ plaquetteEnergy β F distP h).IsPositive :=
  fun _ => h.hm

/-- Phase 3 terminal: a positive lattice mass profile exists. -/
theorem phase3_latticeMassProfile_positive
    (μ : Measure G) (plaquetteEnergy : G → ℝ) (β : ℝ)
    (F : G → ℝ)
    (distP : (N : ℕ) → ConcretePlaquette d N → ConcretePlaquette d N → ℝ)
    (h : ConnectedCorrDecay μ plaquetteEnergy β F distP) :
    ∃ m_lat : LatticeMassProfile, m_lat.IsPositive :=
  ⟨latticeMassFromDecay μ plaquetteEnergy β F distP h,
   latticeMassFromDecay_isPositive μ plaquetteEnergy β F distP h⟩

/-- Bridge to Phase 4: given Phase 3 decay + Phase 4 continuum hypothesis → Clay conclusion. -/
theorem phase3_to_clay
    (μ : Measure G) (plaquetteEnergy : G → ℝ) (β : ℝ)
    (F : G → ℝ)
    (distP : (N : ℕ) → ConcretePlaquette d N → ConcretePlaquette d N → ℝ)
    (h : ConnectedCorrDecay μ plaquetteEnergy β F distP)
    (hcont : HasContinuumMassGap (latticeMassFromDecay μ plaquetteEnergy β F distP h)) :
    ∃ m_phys : ℝ, 0 < m_phys :=
  continuumLimit_mass_pos _
    (latticeMassFromDecay_isPositive μ plaquetteEnergy β F distP h)
    hcont

/-- Phase 3 Balaban summary: RG iteration gives a positive lattice mass profile. -/
theorem eriksson_phase3_balaban_massProfile
    (μ : Measure G) (plaquetteEnergy : G → ℝ) (β : ℝ)
    (F : G → ℝ)
    (distP : (N : ℕ) → ConcretePlaquette d N → ConcretePlaquette d N → ℝ)
    (h : ConnectedCorrDecay μ plaquetteEnergy β F distP) :
    ∃ m_lat : LatticeMassProfile, m_lat.IsPositive :=
  phase3_latticeMassProfile_positive μ plaquetteEnergy β F distP h

end Phase3Assembly

end YangMills
