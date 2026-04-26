/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cowork agent (Claude), under supervision of Lluis Eriksson
-/
import Mathlib
import YangMills.ClayCore.AbelianU1Unconditional
import YangMills.ClayCore.ClusterCorrelatorBound
import YangMills.L8_Terminal.ConnectedCorrDecayBundle

/-!
# First unconditional inhabitant of `ClayYangMillsPhysicalStrong` for SU(1)

This module produces the **first concrete unconditional inhabitant** of
`ClayYangMillsPhysicalStrong` — the strongest current Clay-grade target
predicate in this repository — at `N_c = 1`.

## Strategy

For SU(1), the special unitary group is the singleton `{1}`, so every
Wilson observable is constant and the connected correlator vanishes
identically (`wilsonConnectedCorr_su1_eq_zero`). Therefore the
`ClusterCorrelatorBound 1 r C_clust` predicate holds **vacuously** for
any positive `r ∈ (0, 1)` and any positive `C_clust`: the LHS is `0`
which is bounded by any nonnegative quantity.

Composing with the existing L8 terminal route
`physicalStrong_of_clusterCorrelatorBound_physicalClayDimension_siteDist_measurableF`
yields `ClayYangMillsPhysicalStrong` at the physical Clay dimension
`d = 4` for any Wilson observable `F` with `|F| ≤ 1` and any positive
inverse coupling `β`.

## Importance

This is **structurally analogous** to the existing
`u1_clay_yangMills_mass_gap_unconditional : ClayYangMillsMassGap 1`
in `AbelianU1Unconditional.lean`, but at a **stronger predicate level**:

* `ClayYangMillsMassGap N_c` — existential mass gap structure
  (already had unconditional N_c=1 witness as of 2026-04-23).
* `ClayYangMillsPhysicalStrong` — composite Clay-grade predicate
  combining lattice mass profile + physical observable structure
  (NEW in this file).

Per `COWORK_FINDINGS.md` Finding 003, the SU(1) case is physics-
degenerate (trivial group, no gauge fluctuations). Per Finding 004,
the continuum half is satisfied via the coordinated-scaling artifact.
This witness is therefore **structurally non-vacuous** at the predicate
type level, but **physics-vacuous** at the Yang-Mills mass gap content
level. Its purpose is to demonstrate that `ClayYangMillsPhysicalStrong`
is inhabitable in the project's Lean model, removing any concern that
the predicate is hidden-`False`.

## Caveats

* SU(1) means `Matrix.specialUnitaryGroup (Fin 1) ℂ` (the trivial group
  `{1}`), NOT abelian QED-like U(1) (which would use
  `unitaryGroup (Fin 1)`).
* For physically meaningful cases (N_c ≥ 2), the connected correlator
  is not identically zero, and the witness must come from genuine
  analytic content via the F3 cluster expansion (Branch I, Codex's
  active work) or from independent routes (Branch III RP, etc.).

## Oracle target

Per project discipline (`CODEX_CONSTRAINT_CONTRACT.md` HR5), every
theorem in this file should print
`[propext, Classical.choice, Quot.sound]`.

-/

namespace YangMills

open Real

/-! ## §1. ClusterCorrelatorBound for SU(1) is unconditional -/

/-- For SU(1), the cluster correlator bound holds unconditionally.

    The connected correlator vanishes identically (`wilsonConnectedCorr_su1_eq_zero`),
    so for any positive `r ∈ (0, 1)` and any positive `C_clust`, the inequality
    `|wilsonConnectedCorr ...| ≤ C_clust * exp(...)` reduces to
    `0 ≤ C_clust * exp(-(kpParameter r) * dist)`, which holds because both
    factors are nonnegative.

    This is the SU(1) analogue of `unconditionalU1CorrelatorBound`
    (in `AbelianU1Unconditional.lean`), packaged for the
    `ClusterCorrelatorBound` predicate consumed by the L8 physical
    terminal route. -/
theorem clusterCorrelatorBound_su1_unconditional
    (r : ℝ) (_hr_pos : 0 < r) (_hr_lt1 : r < 1)
    (C_clust : ℝ) (hC : 0 < C_clust) :
    ClusterCorrelatorBound 1 r C_clust := by
  intro d L _instD _instL β _hβ F _hF p q _hdist
  -- LHS: |wilsonConnectedCorr (sunHaarProb 1) ... β F p q|
  -- By wilsonConnectedCorr_su1_eq_zero, this equals 0.
  rw [wilsonConnectedCorr_su1_eq_zero]
  -- Goal: |0| ≤ C_clust * exp(-(kpParameter r) * siteLatticeDist p.site q.site)
  rw [abs_zero]
  -- Goal: 0 ≤ C_clust * exp(...)
  exact mul_nonneg hC.le (Real.exp_nonneg _)

#print axioms clusterCorrelatorBound_su1_unconditional

/-! ## §2. ClayYangMillsPhysicalStrong for SU(1) — UNCONDITIONAL ⭐ -/

/-- **First unconditional inhabitant of `ClayYangMillsPhysicalStrong`**
    for `N_c = 1` and the physical Clay dimension `d = 4`.

    Composes the unconditional `ClusterCorrelatorBound 1 (1/2) 1` (proven
    via `clusterCorrelatorBound_su1_unconditional` above, which uses
    `wilsonConnectedCorr_su1_eq_zero`) with the existing L8 terminal
    route `physicalStrong_of_clusterCorrelatorBound_physicalClayDimension_siteDist_measurableF`.

    Choice of constants (arbitrary, all bounds vacuously satisfied
    for SU(1)):
    * decay rate `r := 1/2`, so `kpParameter r = -log(1/2)/2 = log 2 / 2 > 0`
    * prefactor `C_clust := 1`

    This is the strongest unconditional Clay-grade witness currently
    available in the project for any `N_c`. Caveats apply (see file
    docstring): SU(1) is physics-degenerate, but the witness is
    Lean-structurally non-vacuous. -/
theorem clayYangMillsPhysicalStrong_su1_unconditional
    (β : ℝ) (hβ : 0 < β)
    (F : ↑(Matrix.specialUnitaryGroup (Fin 1) ℂ) → ℝ)
    (hF : ∀ U, |F U| ≤ 1) (hF_meas : Measurable F) :
    ClayYangMillsPhysicalStrong
      (sunHaarProb 1) (wilsonPlaquetteEnergy 1) β F
      (fun (L : ℕ) (p q : ConcretePlaquette physicalClayDimension L) =>
        siteLatticeDist p.site q.site) :=
  physicalStrong_of_clusterCorrelatorBound_physicalClayDimension_siteDist_measurableF
    (1/2 : ℝ) (by norm_num) (by norm_num)
    1 one_pos
    (clusterCorrelatorBound_su1_unconditional (1/2) (by norm_num) (by norm_num) 1 one_pos)
    β F hβ hF hF_meas

#print axioms clayYangMillsPhysicalStrong_su1_unconditional

/-! ## §3. Derived SU(1) unconditional witnesses across the Clay-grade chain -/

/-- **`ClayWitnessHyp 1` — unconditional**.

    Composes `clusterCorrelatorBound_su1_unconditional` with
    `clayWitnessHyp_of_clusterCorrelatorBound`. Carries the same constants
    `r := 1/2`, `C_clust := 1`, with the universal correlator bound
    inherited from the SU(1) connected-correlator vanishing. -/
noncomputable def clayWitnessHyp_su1_unconditional : ClayWitnessHyp 1 :=
  clayWitnessHyp_of_clusterCorrelatorBound 1
    (1/2 : ℝ) (by norm_num) (by norm_num)
    1 one_pos
    (clusterCorrelatorBound_su1_unconditional (1/2) (by norm_num) (by norm_num) 1 one_pos)

#print axioms clayWitnessHyp_su1_unconditional

/-- **`CharacterExpansionData 1` — unconditional**.

    Composes `clusterCorrelatorBound_su1_unconditional` with
    `wilsonCharExpansion`. The Peter-Weyl metadata fields (`Rep`,
    `character`, `coeff`) are filled with the standard `PUnit` /
    zero placeholders (per project's `vestigial-metadata` finding,
    `CLAY_CONVERGENCE_MAP.md` §5). -/
noncomputable def characterExpansionData_su1_unconditional : CharacterExpansionData 1 :=
  wilsonCharExpansion 1
    (1/2 : ℝ) (by norm_num) (by norm_num)
    1 one_pos
    (clusterCorrelatorBound_su1_unconditional (1/2) (by norm_num) (by norm_num) 1 one_pos)

#print axioms characterExpansionData_su1_unconditional

/-! ## §3.5. SUNWilsonClusterMajorisation 1 — second route to ClayMassGap -/

/-- **`SUNWilsonClusterMajorisation 1` — unconditional via `ClusterCorrelatorBound 1`**.

    Constructs the cluster majorisation structure directly from the
    SU(1) connected-correlator vanishing argument. Provides a parallel
    route to `ClayYangMillsMassGap 1` independent of the existing
    `unconditionalU1CorrelatorBound → U1CorrelatorBound → ClayWitnessHyp`
    chain in `AbelianU1Witness.lean`.

    Both routes converge on `ClayYangMillsMassGap 1`:
    - existing route via `U1CorrelatorBound`
    - this route via `ClusterCorrelatorBound 1` (Phase 43) directly

    The SUNWilsonClusterMajorisation form is the canonical input to
    `clay_yangMills_unconditional` in `ClayUnconditional.lean`. -/
noncomputable def sunWilsonClusterMajorisation_su1_unconditional :
    SUNWilsonClusterMajorisation 1 where
  r := 1/2
  hr_pos := by norm_num
  hr_lt_one := by norm_num
  C_clust := 1
  hC_clust := one_pos
  hbound := by
    intro d _ L _ β _hβ F _hF_bdd p q hdist
    -- Same as clusterCorrelatorBound_su1_unconditional core argument
    rw [wilsonConnectedCorr_su1_eq_zero]
    rw [abs_zero]
    exact mul_nonneg one_pos.le (Real.exp_nonneg _)

#print axioms sunWilsonClusterMajorisation_su1_unconditional

/-- **Second route to `ClayYangMillsMassGap 1`** via the new majorisation
    construction. Composes with `clay_yangMills_unconditional` from
    `ClayUnconditional.lean`.

    This is **definitionally** the same as the existing
    `u1_clay_yangMills_mass_gap_unconditional` via the standard adapter,
    but built through Phase 43's `ClusterCorrelatorBound`-based path. -/
noncomputable def clay_yangMills_mass_gap_su1_via_clusterCorrelator :
    ClayYangMillsMassGap 1 :=
  clay_yangMills_unconditional sunWilsonClusterMajorisation_su1_unconditional

#print axioms clay_yangMills_mass_gap_su1_via_clusterCorrelator

/-! ## §4. Meta-theorem: complete SU(1) Clay chain inhabitation -/

/-- **Meta-theorem: every Clay-grade predicate has an SU(1) unconditional witness.**

    Returns a tuple of inhabitants for the principal Clay-grade predicates,
    all derived from the SU(1) connected-correlator vanishing. The witnesses
    are physics-degenerate (per `COWORK_FINDINGS.md` Findings 003/004) but
    Lean-structurally non-vacuous: every predicate type is inhabitable.

    This serves as a lower-bound existential anchor for the project's
    Clay-grade target hierarchy: any future N_c ≥ 2 unconditional witness
    (via Codex's F3 chain or alternative routes) lands in the same
    structurally-inhabitable predicate types. -/
theorem su1_complete_clay_chain_unconditional :
    (∃ _h : ClusterCorrelatorBound 1 (1/2) 1, True) ∧
    (∃ _h : ClayWitnessHyp 1, True) ∧
    (∃ _h : CharacterExpansionData 1, True) ∧
    (∃ _h : ClayYangMillsMassGap 1, True) ∧
    True := by  -- Note: ClayYangMillsPhysicalStrong is parametric in (β, F),
                -- so cannot be packaged as a single existential here.
  refine ⟨⟨?_, trivial⟩, ⟨?_, trivial⟩, ⟨?_, trivial⟩, ⟨?_, trivial⟩, trivial⟩
  · exact clusterCorrelatorBound_su1_unconditional (1/2) (by norm_num) (by norm_num) 1 one_pos
  · exact clayWitnessHyp_su1_unconditional
  · exact characterExpansionData_su1_unconditional
  · exact u1_clay_yangMills_mass_gap_unconditional

#print axioms su1_complete_clay_chain_unconditional

/-! ## §5. Coordination note -/

/-
This file is the SU(1) analogue of `AbelianU1Unconditional.lean` lifted
from `ClayYangMillsMassGap` to the stronger `ClayYangMillsPhysicalStrong`
predicate.

**Cowork session 2026-04-25 Phase 43**:
* Identifies that `ClusterCorrelatorBound 1 r C_clust` is unconditional
  (LHS vanishes by `wilsonConnectedCorr_su1_eq_zero`).
* Composes with the L8 terminal route to produce
  `ClayYangMillsPhysicalStrong` at SU(1) and `d = 4`.
* No Mathlib upstream dependencies; uses only existing project
  infrastructure.

**Strategic role**: provides the FIRST proof that
`ClayYangMillsPhysicalStrong` has any inhabitant at all, removing
"hidden-False" concerns about the predicate. For physically
meaningful cases (N_c ≥ 2), the witness must come from Codex's F3
chain (currently at v2.15.0 with terminal route `physicalStrong_of_graphAnimalShiftedCount1296_siteDist_measurableF`).

Cross-references:
- `AbelianU1Unconditional.lean` — original SU(1) `ClayYangMillsMassGap` witness.
- `COWORK_FINDINGS.md` Finding 003 — SU(1) physics degeneracy caveat.
- `COWORK_FINDINGS.md` Finding 004 — coordinated-scaling continuum
  half caveat (also relevant here).
- `CLAY_CONVERGENCE_MAP.md` — cross-branch composition map.
-/

end YangMills
