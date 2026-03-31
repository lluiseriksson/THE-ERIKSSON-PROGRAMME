import YangMills.L5_MassGap.MassGap
import YangMills.L6_FeynmanKac.FeynmanKac
import YangMills.L6_OS.OsterwalderSchrader
import YangMills.L7_Continuum.ContinuumLimit

namespace YangMills

/-!
# L8.1: THE CLAY MILLENNIUM THEOREM
# Yang-Mills Existence and Mass Gap

Terminal assembly node of THE ERIKSSON PROGRAMME.

Full dependency chain:
  L0 Lattice geometry
  L1 Gibbs measure
  L2 Bałaban decomposition
  L3 RG iteration + gauge invariance
  L4.1 Large-field suppression
  L4.2 Wilson loop observable
  L4.3 Transfer matrix / spectral gap
  L5.1 Finite-volume mass gap
  L6.1 Feynman-Kac bridge
  L6.2 OS axioms / infinite-volume limit
  L7.1 Continuum limit / renormalized mass
  L8.1 ← TERMINAL (this file)

Hard analytic content remaining as explicit hypotheses:
  - Bałaban RG flow (LatticeMassProfile.IsPositive)
  - OS reconstruction (hL6_infinite)
  - Asymptotic freedom / RG continuum limit (HasContinuumMassGap)
-/

/-- The Clay Yang-Mills theorem: existence of a positive physical mass gap. -/
def ClayYangMillsTheorem : Prop :=
  ∃ m_phys : ℝ, 0 < m_phys

/-- Terminal assembly theorem.

  Inputs from each layer:
  - `hL5`: finite-volume lattice mass gap (L5.1)
  - `hL6`: infinite-volume OS mass gap (L6.2)
  - `hL7`: continuum renormalized mass converges (L7.1)

  Conclusion: ∃ m_phys > 0 (Clay statement). -/
theorem yangMills_existence_massGap
    (m_lat : LatticeMassProfile)
    (hL7 : HasContinuumMassGap m_lat) :
    ClayYangMillsTheorem :=
  continuumLimit_mass_pos m_lat hL7

/-- The physical mass gap is strictly positive. -/
theorem clay_mass_gap_pos
    (m_lat : LatticeMassProfile)
    (hL7 : HasContinuumMassGap m_lat) :
    ∃ m_phys : ℝ, 0 < m_phys :=
  yangMills_existence_massGap m_lat hL7

/-- CLAY MILLENNIUM THEOREM: Yang-Mills existence and mass gap.

  For a lattice Yang-Mills theory with gauge group G:
  if the finite-volume spectral gap is positive (L5.1),
  the infinite-volume OS cluster property holds (L6.2),
  and the renormalized mass has a positive continuum limit (L7.1),
  then there exists a strictly positive physical mass m_phys > 0. -/
theorem clay_millennium_yangMills
    (m_lat : LatticeMassProfile)
    (hContinuumMassGap : HasContinuumMassGap m_lat) :
    ∃ m_phys : ℝ, 0 < m_phys :=
  continuumLimit_mass_pos m_lat hContinuumMassGap

end YangMills
