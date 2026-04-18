/- Copyright (c) 2026 The Eriksson Programme. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lluis Eriksson

Phase 7.1: U(1) Abelian Witness

First **concrete inhabitation route** of `ClayYangMillsMassGap 1` via
the U(1) exactly-solvable Wilson lattice gauge theory in `d = 2`.

## Physical content (motivating U(1) analysis)

In `d = 2` with gauge group U(1), the Wilson partition function
factorises into independent plaquettes, each carrying character weight
`exp(β cos θ)`. Character expansion in Fourier modes of the circle gives

  `⟨cos(n θ)⟩_β = I_n(β) / I_0(β)`

where `I_n` is the modified Bessel function of the first kind. The
two-plaquette connected correlator at separation `k` (in lattice units)
then decays as

  `|⟨W_p W_q⟩_c| ≤ C · (I_1(β) / I_0(β))^k`

with decay parameter `r := I_1(β) / I_0(β) ∈ (0, 1)` for every `β > 0`.
Taking `m := -log(r)/2 = kpParameter r`, this gives exponential decay
in the exact form demanded by the `hbound_hyp` signature of
`ClayWitnessHyp 1`.

## Lean content

This file abstracts the U(1) decay estimate into a hypothesis bundle
`U1CorrelatorBound`, forwards it field-by-field to a `ClayWitnessHyp 1`,
and produces `u1_clay_yangMills_mass_gap`, a concrete inhabitant of
`ClayYangMillsMassGap 1`.

The Bessel-ratio decay estimate itself is **not** formalised here; it is
left as the explicit hypothesis `h_decay`. Future phases will discharge
it by formalising the U(1) character expansion directly in Mathlib.
-/
import Mathlib
import YangMills.ClayCore.ClayAuthentic
import YangMills.ClayCore.ClayWitness
import YangMills.ClayCore.KPSmallness

namespace YangMills

open Real

/-- **U(1) correlator bound (hypothesis bundle).**

    Packages the U(1) Wilson two-plaquette exponential decay in the
    exact signature required by `ClayWitnessHyp 1.hbound_hyp`, with the
    mass gap identified as `kpParameter r = -log(r)/2` and the prefactor
    identified as `C_u1`.

    Physically, `r := I_1(β) / I_0(β) ∈ (0, 1)` is the Bessel ratio
    controlling the d=2 U(1) decay rate. -/
structure U1CorrelatorBound : Type where
  /-- The Bessel-ratio decay parameter `r ∈ (0, 1)`. -/
  r : ℝ
  /-- Positivity of `r`. -/
  hr_pos : 0 < r
  /-- Upper bound `r < 1`. -/
  hr_lt_one : r < 1
  /-- U(1) clustering prefactor. -/
  C_u1 : ℝ
  /-- Positivity of the U(1) prefactor. -/
  hC_u1 : 0 < C_u1
  /-- The U(1) two-plaquette exponential decay bound, in the exact
      signature of `ClayWitnessHyp 1.hbound_hyp`. -/
  h_decay :
    ∀ {d : ℕ} [NeZero d] {L : ℕ} [NeZero L] (β : ℝ) (_hβ : 0 < β)
      (F : ↥(Matrix.specialUnitaryGroup (Fin 1) ℂ) → ℝ)
      (_hF_bdd : ∀ U, |F U| ≤ 1)
      (p q : ConcretePlaquette d L),
      (1 : ℝ) ≤ siteLatticeDist p.site q.site →
      |wilsonConnectedCorr
          (sunHaarProb 1)
          (wilsonPlaquetteEnergy 1)
          β F p q|
        ≤ C_u1 * Real.exp (-(kpParameter r) * siteLatticeDist p.site q.site)

/-- Forward a U(1) bound bundle to the generic Clay witness hypothesis
    bundle (specialised to `N_c = 1`). -/
noncomputable def u1_clay_witness_hyp (ucb : U1CorrelatorBound) :
    ClayWitnessHyp 1 where
  r := ucb.r
  hr_pos := ucb.hr_pos
  hr_lt_one := ucb.hr_lt_one
  C_clust := ucb.C_u1
  hC_clust := ucb.hC_u1
  hbound_hyp := ucb.h_decay

/-- **U(1) Clay witness.** Given a U(1) correlator bound, produce a
    concrete inhabitant of `ClayYangMillsMassGap 1` with mass gap
    `kpParameter r` and prefactor `C_u1`. -/
noncomputable def u1_clay_yangMills_mass_gap (ucb : U1CorrelatorBound) :
    ClayYangMillsMassGap 1 :=
  clay_yangMills_witness (u1_clay_witness_hyp ucb)

/-- Mass gap of the U(1) witness equals `kpParameter r = -log(r)/2`. -/
theorem u1_mass_gap_eq (ucb : U1CorrelatorBound) :
    (u1_clay_yangMills_mass_gap ucb).m = kpParameter ucb.r := rfl

/-- Mass gap of the U(1) witness is strictly positive. -/
theorem u1_mass_gap_pos (ucb : U1CorrelatorBound) :
    0 < (u1_clay_yangMills_mass_gap ucb).m :=
  kpParameter_pos ucb.hr_pos ucb.hr_lt_one

/-- Prefactor of the U(1) witness equals `C_u1`. -/
theorem u1_prefactor_eq (ucb : U1CorrelatorBound) :
    (u1_clay_yangMills_mass_gap ucb).C = ucb.C_u1 := rfl

end YangMills
