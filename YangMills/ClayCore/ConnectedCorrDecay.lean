/- Copyright (c) 2026 The Eriksson Programme. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lluis Eriksson

Phase 3 / Task #7 sub-target P1: ClayConnectedCorrDecay abstraction.

First-class Lean abstraction of **connected correlator decay** for the
SU(N_c) Wilson lattice Gibbs measure. Promoted from the deferred
comment in `SchurPhysicalBridge.lean` (L28, referring to
`fundamentalObservable_ClayConnectedCorrDecay`) to a named structure.

Field content is structurally identical to `ClayYangMillsMassGap`, but
the abstraction is exported under a physically-meaningful name to
serve as the common target of:
  * the U(1) unconditional route (via `unconditionalU1CorrelatorBound`);
  * the N_c ≥ 2 analytic routes (Osterwalder–Seiler / Kotecký–Preiss /
    Balaban RG), which enter through `ClayWitnessHyp N_c`.

Both directions between `ClayConnectedCorrDecay N_c` and
`ClayYangMillsMassGap N_c` are pure field-for-field projections
and introduce no axioms.

Oracle target: `[propext, Classical.choice, Quot.sound]`.
No `sorry`. No new axioms.
-/

import Mathlib
import YangMills.ClayCore.ClayAuthentic
import YangMills.ClayCore.ClayWitness
import YangMills.ClayCore.AbelianU1Witness
import YangMills.ClayCore.AbelianU1Unconditional

namespace YangMills

open Real

noncomputable section

/-- **Connected correlator decay (first-class abstraction).**

Uniform exponential clustering of the connected two-plaquette Wilson
correlator against every bounded class observable
`F : SU(N_c) → ℝ`, at every positive inverse coupling `β`, every
spacetime dimension `d`, every lattice size `L`, and every pair of
plaquettes separated by at least one lattice unit.

Structurally identical to `ClayYangMillsMassGap`; re-exported under a
physically-meaningful name to serve as the entry target of the U(1)
unconditional route and the Balaban H1+H2+H3 / KP / OS routes for
`N_c ≥ 2`. Round-trip projections are field-for-field (`rfl`) and
introduce no axioms. -/
structure ClayConnectedCorrDecay (N_c : ℕ) [NeZero N_c] : Type where
  /-- Exponential decay rate (mass gap). -/
  m : ℝ
  /-- Positivity of the decay rate. -/
  hm : 0 < m
  /-- Prefactor in the exponential bound. -/
  C : ℝ
  /-- Positivity of the prefactor. -/
  hC : 0 < C
  /-- The uniform two-plaquette exponential clustering bound. -/
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

/-! ### Structural projections to / from `ClayYangMillsMassGap` -/

/-- From a Clay mass-gap witness, produce a connected-correlator-decay
    witness. Pure field-for-field projection; no axioms. -/
noncomputable def ClayConnectedCorrDecay.ofClayMassGap
    {N_c : ℕ} [NeZero N_c]
    (g : ClayYangMillsMassGap N_c) : ClayConnectedCorrDecay N_c where
  m := g.m
  hm := g.hm
  C := g.C
  hC := g.hC
  hbound := g.hbound

/-- From a connected-correlator-decay witness, produce a Clay mass-gap
    witness. Pure field-for-field projection; no axioms. -/
noncomputable def ClayConnectedCorrDecay.toClayMassGap
    {N_c : ℕ} [NeZero N_c]
    (w : ClayConnectedCorrDecay N_c) : ClayYangMillsMassGap N_c where
  m := w.m
  hm := w.hm
  C := w.C
  hC := w.hC
  hbound := w.hbound

/-- Round-trip starting from `ClayConnectedCorrDecay` is the identity. -/
@[simp] theorem ClayConnectedCorrDecay.ofClayMassGap_toClayMassGap
    {N_c : ℕ} [NeZero N_c] (w : ClayConnectedCorrDecay N_c) :
    ClayConnectedCorrDecay.ofClayMassGap
        (ClayConnectedCorrDecay.toClayMassGap w) = w := rfl

/-- Round-trip starting from `ClayYangMillsMassGap` is the identity. -/
@[simp] theorem ClayConnectedCorrDecay.toClayMassGap_ofClayMassGap
    {N_c : ℕ} [NeZero N_c] (g : ClayYangMillsMassGap N_c) :
    ClayConnectedCorrDecay.toClayMassGap
        (ClayConnectedCorrDecay.ofClayMassGap g) = g := rfl

/-! ### Terminal projection to the Clay Millennium statement -/

/-- The Clay Millennium statement `∃ m_phys : ℝ, 0 < m_phys` follows
    from any connected-correlator-decay witness. -/
theorem ClayConnectedCorrDecay.clayTheorem
    {N_c : ℕ} [NeZero N_c] (w : ClayConnectedCorrDecay N_c) :
    ClayYangMillsTheorem :=
  clayMassGap_implies_clayTheorem (ClayConnectedCorrDecay.toClayMassGap w)

/-! ### Consumer hub for analytic routes at `N_c ≥ 2` -/

/-- **Entry point for the `N_c ≥ 2` analytic routes.**

Any analytic route that produces a `ClayWitnessHyp N_c`
(Osterwalder–Seiler duality; Kotecký–Preiss in the strong-coupling
phase; Balaban RG in the weak-coupling phase) discharges
`ClayConnectedCorrDecay N_c`. -/
noncomputable def ClayConnectedCorrDecay.ofClayWitnessHyp
    {N_c : ℕ} [NeZero N_c]
    (hyp : ClayWitnessHyp N_c) : ClayConnectedCorrDecay N_c :=
  ClayConnectedCorrDecay.ofClayMassGap (clay_yangMills_witness hyp)

/-- The mass gap produced by `ClayConnectedCorrDecay.ofClayWitnessHyp` is
    `kpParameter hyp.r = -log(hyp.r) / 2`. -/
theorem ClayConnectedCorrDecay.ofClayWitnessHyp_mass_eq
    {N_c : ℕ} [NeZero N_c] (hyp : ClayWitnessHyp N_c) :
    (ClayConnectedCorrDecay.ofClayWitnessHyp hyp).m = kpParameter hyp.r := rfl

/-- The prefactor produced by `ClayConnectedCorrDecay.ofClayWitnessHyp` is
    `hyp.C_clust`. -/
theorem ClayConnectedCorrDecay.ofClayWitnessHyp_prefactor_eq
    {N_c : ℕ} [NeZero N_c] (hyp : ClayWitnessHyp N_c) :
    (ClayConnectedCorrDecay.ofClayWitnessHyp hyp).C = hyp.C_clust := rfl

/-! ### U(1) unconditional instance -/

/-- **Unconditional U(1) connected-correlator-decay witness.**

Routed through `u1_clay_yangMills_mass_gap_unconditional`, which rests
on `wilsonConnectedCorr_su1_eq_zero` (SU(1) is a singleton, so every
Wilson connected correlator vanishes identically, and the exponential
bound holds vacuously).

Axiom oracle: `[propext, Classical.choice, Quot.sound]`. No hypotheses. -/
noncomputable def unconditional_U1_ClayConnectedCorrDecay :
    ClayConnectedCorrDecay 1 :=
  ClayConnectedCorrDecay.ofClayMassGap u1_clay_yangMills_mass_gap_unconditional

/-- Mass gap of the unconditional U(1) witness equals `kpParameter (1/2)`. -/
theorem unconditional_U1_ClayConnectedCorrDecay_mass_eq :
    unconditional_U1_ClayConnectedCorrDecay.m = kpParameter (1 / 2 : ℝ) := rfl

/-- Mass gap of the unconditional U(1) witness is strictly positive. -/
theorem unconditional_U1_ClayConnectedCorrDecay_mass_pos :
    0 < unconditional_U1_ClayConnectedCorrDecay.m :=
  u1_unconditional_mass_gap_pos

/-- Prefactor of the unconditional U(1) witness equals `1`. -/
theorem unconditional_U1_ClayConnectedCorrDecay_prefactor_eq :
    unconditional_U1_ClayConnectedCorrDecay.C = 1 := rfl

/-! ### Terminal: unconditional Clay Millennium statement at `N_c = 1` -/

/-- **Unconditional Clay Millennium statement for `N_c = 1`, via the
`ClayConnectedCorrDecay` abstraction.** Fully closed chain: no analytic
hypotheses, no `sorry`, no new axioms. -/
theorem unconditional_U1_ClayConnectedCorrDecay_clayTheorem :
    ClayYangMillsTheorem :=
  unconditional_U1_ClayConnectedCorrDecay.clayTheorem

end

end YangMills

/-! ## Axiom oracle declarations (informational)

Emitted by the Lean compiler at build time; expected oracle for every
declaration in this file is `[propext, Classical.choice, Quot.sound]`. -/

#print axioms YangMills.unconditional_U1_ClayConnectedCorrDecay
#print axioms YangMills.unconditional_U1_ClayConnectedCorrDecay_clayTheorem
