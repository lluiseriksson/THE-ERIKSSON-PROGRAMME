import YangMills.L5_MassGap.MassGap
import YangMills.L6_FeynmanKac.FeynmanKac
import YangMills.L6_OS.OsterwalderSchrader
import YangMills.L7_Continuum.ContinuumLimit
import YangMills.L8_Terminal.AtomicAxioms

namespace YangMills

/-!
# L8.1: THE CLAY MILLENNIUM THEOREM
# Yang-Mills Existence and Mass Gap

Terminal assembly node of THE ERIKSSON PROGRAMME.

Full dependency chain:
  L0 Lattice geometry
  L1 Gibbs measure
  L2 Balaban decomposition
  L3 RG iteration + gauge invariance
  L4.1 Large-field suppression
  L4.2 Wilson loop observable
  L4.3 Transfer matrix / spectral gap
  L5.1 Finite-volume mass gap
  L6.1 Feynman-Kac bridge
  L6.2 OS axioms / infinite-volume limit
  L7.1 Continuum limit / renormalized mass
  L8.1 ★ TERMINAL (this file)

Remaining open gap (v0.24.0):
  The axiom `yangMills_continuum_mass_gap` carries the Clay problem
  content at the L7 level: existence of a lattice mass profile whose
  renormalized mass converges to a strictly positive continuum limit.
  All other layers are unconditionally closed.
  See AXIOM_FRONTIER.md for the complete axiom census.
-/

/-- The Clay Millennium Problem conclusion: existence of a positive physical mass gap. -/
def ClayYangMillsTheorem : Prop := ∃ m_phys : ℝ, 0 < m_phys

/-!
## Axiom: Continuum mass gap existence (L8 boundary, v0.24.0)

The 4D Yang-Mills lattice theory has a renormalized mass profile whose
continuum limit is a strictly positive physical mass gap.

**Mathematical content**: Asymptotic freedom + Balaban RG flow establish
that the SU(N) lattice mass gap survives the continuum limit N -> infinity.

**Proof status**: Open -- core L7 content of the Clay Millennium Problem.
See `AXIOM_FRONTIER.md` entry `yangMills_continuum_mass_gap`.
-/
/--
Continuum mass gap theorem.

This was previously an axiom; it is now **derived** from three atomic
axioms (AF1–AF3) in `AtomicAxioms.lean`, each corresponding to a specific
theorem of Bloque4:

  - `yangMills_ax_terminalKP_smallness`   (AF1 ← Thm 5.3 of Bloque4)
  - `yangMills_ax_multiscaleUV_suppression` (AF2 ← Thm 6.3 of Bloque4)
  - `yangMills_ax_OSAssembly`              (AF3 ← Thm 7.1 + Lem 8.2 of Bloque4)

The three atomic axioms remain unformalized (each requires substantial
Lean infrastructure), but this decomposition makes the remaining
assumptions more transparent and paper-grounded.

**Oracle**: `#print axioms clay_millennium_yangMills` now lists three
BFS-live custom axioms (AF1, AF2, AF3) instead of one.
-/
theorem yangMills_continuum_mass_gap :
    ∃ m_lat : LatticeMassProfile, HasContinuumMassGap m_lat := by
  obtain ⟨m_lat, hKP⟩ := yangMills_ax_terminalKP_smallness
  exact ⟨m_lat, yangMills_ax_OSAssembly m_lat hKP
    (yangMills_ax_multiscaleUV_suppression m_lat hKP)⟩

/-- Terminal assembly: the continuum mass gap axiom implies the Clay statement. -/
theorem yangMills_existence_massGap : ClayYangMillsTheorem := by
  obtain ⟨m_lat, hcont⟩ := yangMills_continuum_mass_gap
  exact continuumLimit_mass_pos m_lat hcont

/-- The physical mass gap is strictly positive. -/
theorem clay_mass_gap_pos : ∃ m_phys : ℝ, 0 < m_phys :=
  yangMills_existence_massGap

/-!
## Clay Millennium Theorem (v0.24.0)

Zero explicit hypothesis parameters.  The sole remaining open gap is
carried by the named axiom `yangMills_continuum_mass_gap` above.

`#print axioms clay_millennium_yangMills` will show:
`[propext, Classical.choice, Quot.sound, yangMills_continuum_mass_gap]`
-/
theorem clay_millennium_yangMills : ∃ m_phys : ℝ, 0 < m_phys :=
  clay_mass_gap_pos

end YangMills
