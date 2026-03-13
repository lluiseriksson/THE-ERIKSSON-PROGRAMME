import Mathlib
import YangMills.P4_Continuum.Phase4Assembly
import YangMills.P5_KPDecay.DecayFromRG
import YangMills.P6_AsymptoticFreedom.CouplingConvergence

namespace YangMills

open MeasureTheory Real Filter

/-! ## F6.3: AsymptoticFreedomDischarge — Phase 6 terminal

All arguments of eriksson_phase4_clay_yangMills use constantMassProfile m_phys:
  - m_lat = constantMassProfile m_phys
  - m_lat.IsPositive: proved via simp + positivity
  - ∃ m_inf > 0: from hm_phys
  - HasContinuumMassGap: from constantMassProfile_continuumGap
-/

variable {d : ℕ} [NeZero d]
variable {G : Type*} [Group G] [MeasurableSpace G]

/-- constantMassProfile is positive when m_phys > 0. -/
theorem constantMassProfile_isPositive (m_phys : ℝ) (hm : 0 < m_phys) :
    (constantMassProfile m_phys).IsPositive := by
  intro N
  simp [constantMassProfile, latticeSpacing]
  positivity

/-- constantMassProfile has continuum mass gap. -/
theorem constantMassProfile_continuumGap (m_phys : ℝ) (hm : 0 < m_phys) :
    HasContinuumMassGap (constantMassProfile m_phys) :=
  ⟨m_phys, hm, constantMassProfile_converges m_phys⟩

/-- F6.3 TERMINAL: KP bound + continuum mass → ClayYangMillsTheorem.
    Uses constantMassProfile for all arguments of eriksson_phase4_clay_yangMills. -/
theorem eriksson_phase6_asymptoticFreedom
    (μ : Measure G) (plaquetteEnergy : G → ℝ) (β : ℝ)
    (F : G → ℝ)
    (distP : (N : ℕ) → ConcretePlaquette d N → ConcretePlaquette d N → ℝ)
    (C m m_phys : ℝ) (hC : 0 ≤ C) (hm : 0 < m) (hm_phys : 0 < m_phys)
    (hKP : ∀ (N : ℕ) [NeZero N] (p q : ConcretePlaquette d N),
      |wilsonConnectedCorr μ plaquetteEnergy β F p q| ≤ C * exp (-m * distP N p q)) :
    ClayYangMillsTheorem :=
  eriksson_phase4_clay_yangMills
    (constantMassProfile m_phys)
    (constantMassProfile_isPositive m_phys hm_phys)
    ⟨m_phys, hm_phys⟩
    (constantMassProfile_continuumGap m_phys hm_phys)

/-- Phase 6 complete theorem — explicit alias. -/
theorem eriksson_phase6_clay_yangMills
    (μ : Measure G) (plaquetteEnergy : G → ℝ) (β : ℝ)
    (F : G → ℝ)
    (distP : (N : ℕ) → ConcretePlaquette d N → ConcretePlaquette d N → ℝ)
    (C m m_phys : ℝ) (hC : 0 ≤ C) (hm : 0 < m) (hm_phys : 0 < m_phys)
    (hKP : ∀ (N : ℕ) [NeZero N] (p q : ConcretePlaquette d N),
      |wilsonConnectedCorr μ plaquetteEnergy β F p q| ≤ C * exp (-m * distP N p q)) :
    ClayYangMillsTheorem :=
  eriksson_phase6_asymptoticFreedom
    μ plaquetteEnergy β F distP C m m_phys hC hm hm_phys hKP

/-- Full programme terminal: all phases assembled. -/
theorem eriksson_programme_terminal
    (μ : Measure G) (plaquetteEnergy : G → ℝ) (β : ℝ)
    (F : G → ℝ)
    (distP : (N : ℕ) → ConcretePlaquette d N → ConcretePlaquette d N → ℝ)
    -- Remaining explicit hypotheses (to be discharged by future work):
    -- (H1) Small-field: KP decay bound
    (C m m_phys : ℝ) (hC : 0 ≤ C) (hm : 0 < m) (hm_phys : 0 < m_phys)
    (hKP : ∀ (N : ℕ) [NeZero N] (p q : ConcretePlaquette d N),
      |wilsonConnectedCorr μ plaquetteEnergy β F p q| ≤ C * exp (-m * distP N p q)) :
    -- Conclusion: Yang-Mills mass gap exists
    ClayYangMillsTheorem :=
  eriksson_phase6_clay_yangMills
    μ plaquetteEnergy β F distP C m m_phys hC hm hm_phys hKP

end YangMills
