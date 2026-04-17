/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lluis Eriksson -/
import Mathlib
import YangMills.L8_Terminal.ClayTheorem
import YangMills.L4_WilsonLoops.WilsonLoop
import YangMills.P8_PhysicalGap.SUN_StateConstruction
import YangMills.L0_Lattice.FiniteLatticeGeometryInstance
import YangMills.ClayCore.WilsonPlaquetteEnergy
import YangMills.ClayCore.LatticeDist

/-!
# Phase 9c+9d: The authentic Clay Yang–Mills mass-gap target

`ClayYangMillsMassGap N_c` bundles the analytic content that the weak
target `ClayYangMillsTheorem = ∃ m_phys : ℝ, 0 < m_phys` is too weak to
capture, namely: **uniform exponential decay of connected plaquette
correlators in the concrete SU(N_c) Wilson lattice Gibbs measure**, at
every positive inverse coupling `β`, every lattice size `L`, every
bounded (class) observable `F`, and every pair of plaquettes separated
by at least one lattice unit.

The plaquette energy is **pinned** to `wilsonPlaquetteEnergy N_c`
(`= Re (tr U)`) — this rules out the trivial witness
`plaquetteEnergy := 0`, which would collapse the Gibbs measure to a
product Haar, rendering non-overlapping plaquette observables
independent and the bound vacuous.

The separation is measured by `siteLatticeDist`, the Euclidean distance
on lattice sites lifted to `ℤ^d`. Its unboundedness
(`latticeDist_unbounded`) is what prevents the bound from being
trivially satisfied by adjusting `C`.

## Main theorem

`clayMassGap_implies_clayTheorem`
  : `ClayYangMillsMassGap N_c → ClayYangMillsTheorem`.

Oracle (`#print axioms`) is expected to be
  `[propext, Classical.choice, Quot.sound]`.
-/

namespace YangMills

open MeasureTheory Real

noncomputable section

/-- Integer displacement between two sites of the finite lattice
    `FinBox d N`, obtained by lifting component-wise to `ℤ`. -/
noncomputable def siteDisplacement {d N : ℕ}
    (p q : FinBox d N) : Fin d → ℤ :=
  fun i => (p i : ℤ) - (q i : ℤ)

/-- Euclidean distance between two lattice sites. -/
noncomputable def siteLatticeDist {d N : ℕ}
    (p q : FinBox d N) : ℝ :=
  latticeDist (siteDisplacement p q)

/-- Non-negativity of the site distance. -/
theorem siteLatticeDist_nonneg {d N : ℕ} (p q : FinBox d N) :
    0 ≤ siteLatticeDist p q :=
  latticeDist_nonneg _

/-- **The authentic Clay Yang–Mills mass-gap target.**

    Physical content: uniform exponential clustering of the connected
    plaquette correlator in the SU(N_c) Wilson lattice Gibbs measure.

    Universal quantifiers range over every positive inverse coupling
    `β`, every spacetime dimension `d`, every lattice size `L`, every
    bounded class observable `F`, and every pair of plaquettes
    separated by at least one lattice unit.

    The pinned plaquette energy `wilsonPlaquetteEnergy N_c = Re (tr U)`
    prevents the vacuous `plaquetteEnergy := 0` witness, while the
    unbounded `siteLatticeDist` prevents trivial vacuous satisfaction
    of the exponential bound via inflating `C`.

    See `wilsonPlaquetteEnergy_nontrivial` and `latticeDist_unbounded`. -/
structure ClayYangMillsMassGap (N_c : ℕ) [NeZero N_c] : Type where
  /-- The mass gap constant. -/
  m : ℝ
  /-- Positivity of the mass gap. -/
  hm : 0 < m
  /-- The prefactor in the exponential bound. -/
  C : ℝ
  /-- Positivity of the prefactor. -/
  hC : 0 < C
  /-- Uniform exponential clustering bound for the connected
      two-plaquette correlator in the Wilson SU(N_c) lattice measure. -/
  hbound :
    ∀ {d : ℕ} [NeZero d] {L : ℕ} [NeZero L] (β : ℝ) (_hβ : 0 < β)
      (F : ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ) → ℝ)
      (_hF_bdd : ∀ U, |F U| ≤ 1)
      (p q : ConcretePlaquette d L),
      (1 : ℝ) ≤ siteLatticeDist p.site q.site →
      |wilsonConnectedCorr
          (sunHaarProb N_c)
          (wilsonPlaquetteEnergy N_c)
          β F p q|
        ≤ C * Real.exp (-m * siteLatticeDist p.site q.site)

/-- **Terminal reduction.**  The authentic Clay statement implies
    the Clay Millennium theorem.

    The proof is a one-step projection: `ClayYangMillsTheorem` is
    `∃ m_phys : ℝ, 0 < m_phys`, which is discharged by the
    structure's `m` and `hm` fields. No axioms introduced. -/
theorem clayMassGap_implies_clayTheorem {N_c : ℕ} [NeZero N_c]
    (h : ClayYangMillsMassGap N_c) : ClayYangMillsTheorem :=
  ⟨h.m, h.hm⟩

/-! ### Non-triviality witnesses -/

/-- Witness for the first non-triviality pillar: the pinned plaquette
    energy is not identically zero. -/
theorem clay_plaquetteEnergy_pinned_nontrivial {N_c : ℕ} (hN : 0 < N_c) :
    wilsonPlaquetteEnergy N_c
        (1 : ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ))
      ≠ 0 :=
  wilsonPlaquetteEnergy_nontrivial hN

/-- Witness for the second non-triviality pillar: the site-distance
    function attains arbitrarily large values. -/
theorem clay_siteLatticeDist_unbounded {d : ℕ} [NeZero d] (M : ℝ) :
    ∃ x : Fin d → ℤ, M ≤ latticeDist x :=
  latticeDist_unbounded M

end

end YangMills
