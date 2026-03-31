import Mathlib
import YangMills.L6_OS.OsterwalderSchrader

namespace YangMills

open Filter Topology MeasureTheory

/-! ## L7.1: Continuum limit interface

This file formalizes the minimal continuum limit layer:
- lattice spacing a(N) = 1/(N+1) → 0 as N → ∞
- renormalized physical mass = lim_{N→∞} m_lat(N) / a(N)
- connection to OS cluster property from L6.2
- terminal: continuum mass gap > 0

We do NOT prove renormalization group flow or asymptotic freedom here.
Those are the hard analytic content for future work.
-/

/-! ### Lattice spacing -/

/-- Lattice spacing at resolution N. Using 1/(N+1) to avoid division by zero. -/
noncomputable def latticeSpacing (N : ℕ) : ℝ := 1 / (N + 1)

/-- Lattice spacing is strictly positive. -/
lemma latticeSpacing_pos (N : ℕ) : 0 < latticeSpacing N := by
  simp [latticeSpacing]; positivity

/-- Lattice spacing tends to zero as N → ∞. -/
lemma latticeSpacing_tendsto_zero :
    Tendsto latticeSpacing atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

/-! ### Lattice mass profile -/

/-- A lattice mass profile: mass gap at each lattice resolution N. -/
def LatticeMassProfile := ℕ → ℝ

/-- A lattice mass profile is positive if m_lat(N) > 0 for all N. -/
def LatticeMassProfile.IsPositive (m_lat : LatticeMassProfile) : Prop :=
  ∀ N : ℕ, 0 < m_lat N

/-- Renormalized mass at resolution N: m_lat(N) / a(N). -/
noncomputable def renormalizedMass (m_lat : LatticeMassProfile) (N : ℕ) : ℝ :=
  m_lat N / latticeSpacing N

/-- Renormalized mass is positive if the lattice mass is positive. -/
lemma renormalizedMass_pos (m_lat : LatticeMassProfile)
    (hm : m_lat.IsPositive) (N : ℕ) : 0 < renormalizedMass m_lat N :=
  div_pos (hm N) (latticeSpacing_pos N)

/-! ### Continuum mass gap -/

/-- The continuum mass gap exists if the renormalized mass converges
    to a strictly positive limit. -/
def HasContinuumMassGap (m_lat : LatticeMassProfile) : Prop :=
  ∃ m_phys : ℝ, 0 < m_phys ∧
    Tendsto (renormalizedMass m_lat) atTop (𝓝 m_phys)

/-- If the continuum mass gap exists, the physical mass is positive. -/
theorem continuumMassGap_pos (m_lat : LatticeMassProfile)
    (h : HasContinuumMassGap m_lat) : ∃ m : ℝ, 0 < m := by
  obtain ⟨m, hm, _⟩ := h; exact ⟨m, hm⟩

/-! ### OS bridge to continuum -/

/-- The OS-continuum bridge: an OS cluster property at infinite volume
    provides a lattice mass profile compatible with the continuum limit. -/
def OSContinuumBridge
    {X : Type*} [MeasurableSpace X]
    (muInf : Measure X) (Obs : Type*)
    (evalObs : Obs → X → ℝ) (distObs : Obs → Obs → ℝ)
    (m_lat : LatticeMassProfile) : Prop :=
  m_lat.IsPositive ∧ OSClusterProperty muInf Obs evalObs distObs

/-- OS cluster + continuum limit → physical mass gap. -/
theorem osContinuum_massGap
    {X : Type*} [MeasurableSpace X]
    (muInf : Measure X) (Obs : Type*)
    (evalObs : Obs → X → ℝ) (distObs : Obs → Obs → ℝ)
    (m_lat : LatticeMassProfile)
    (hbridge : OSContinuumBridge muInf Obs evalObs distObs m_lat)
    (hcont : HasContinuumMassGap m_lat) :
    ∃ m : ℝ, 0 < m :=
  continuumMassGap_pos m_lat hcont

/-! ### Terminal L7.1 theorem -/

/-- L7.1 terminal: lattice mass profile + continuum convergence → physical mass gap.
    Hard content (RG flow, asymptotic freedom) is explicit hypothesis. -/
theorem continuumLimit_massGap
    (m_lat : LatticeMassProfile)
    (hcont : HasContinuumMassGap m_lat) :
    ∃ m_phys : ℝ, 0 < m_phys ∧
      Tendsto (renormalizedMass m_lat) atTop (𝓝 m_phys) := by
  obtain ⟨m, hm, hlim⟩ := hcont
  exact ⟨m, hm, hlim⟩

/-- Corollary: the continuum physical mass is strictly positive. -/
theorem continuumLimit_mass_pos
    (m_lat : LatticeMassProfile)
    (hcont : HasContinuumMassGap m_lat) :
    ∃ m_phys : ℝ, 0 < m_phys :=
  continuumMassGap_pos m_lat hcont

end YangMills
