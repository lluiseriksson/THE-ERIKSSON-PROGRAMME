-- TestC72Proto.lean: Phase 5 prototype verification for C72
-- C72-H: HasContinuumMassGap.lattice_mass_tendsto_zero  (goes to DecaySummability.lean)
-- C72-T1: clay_strong_no_axiom  (goes to AsymptoticFreedomDischarge.lean)

import YangMills.P6_AsymptoticFreedom.AsymptoticFreedomDischarge

namespace YangMills

open Filter Topology Real

-- ── C72-H prototype ──────────────────────────────────────────────────────────
-- (DecaySummability.lean only imports ContinuumLimit; proof uses only those)

/-- If a lattice mass profile has a continuum mass gap, then its lattice masses
    tend to zero.  Proof: m_lat N = renormalizedMass m_lat N * latticeSpacing N,
    and renorm → m_phys while a(N) → 0, so the product → 0. -/
theorem test_lattice_mass_tendsto_zero {m_lat : LatticeMassProfile}
    (h : HasContinuumMassGap m_lat) :
    Tendsto m_lat atTop (𝓝 0) := by
  obtain ⟨m_phys, _, htend⟩ := h
  -- m_lat N = renormalizedMass m_lat N * latticeSpacing N (algebraic identity)
  have heq : ∀ N : ℕ, m_lat N = renormalizedMass m_lat N * latticeSpacing N := fun N =>
    (div_mul_cancel₀ (m_lat N) (ne_of_gt (latticeSpacing_pos N))).symm
  have key : Tendsto (fun N : ℕ => renormalizedMass m_lat N * latticeSpacing N) atTop (𝓝 0) := by
    have hmul := htend.mul latticeSpacing_tendsto_zero
    simpa [mul_zero] using hmul
  exact key.congr (fun N => (heq N).symm)

-- ── C72-T1 prototype ─────────────────────────────────────────────────────────

/-- ClayYangMillsStrong is provable without yangMills_continuum_mass_gap.
    Both ClayYangMillsTheorem and ClayYangMillsStrong are vacuously provable.
    The real Clay target must connect m_lat to the actual Yang-Mills theory.
    Oracle: [propext, Classical.choice, Quot.sound]. -/
theorem test_clay_strong_no_axiom : ClayYangMillsStrong :=
  ⟨constantMassProfile 1, constantMassProfile_continuumGap 1 one_pos⟩

end YangMills
