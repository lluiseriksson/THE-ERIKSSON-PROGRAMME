/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cowork agent (Claude), under supervision of Lluis Eriksson
-/
import Mathlib
import YangMills.ClayCore.AbelianU1Unconditional
import YangMills.L7_Continuum.PhysicalSchemeWitness

/-!
# Unconditional `ClayYangMillsPhysicalStrong_Genuine` for SU(1)

This module produces the **first concrete unconditional inhabitant** of
`ClayYangMillsPhysicalStrong_Genuine` — the **strongest** Clay-grade
predicate in this repository, combining genuine `IsYangMillsMassProfile`
content with `HasContinuumMassGap_Genuine` (the non-coordinated-scaling
version of the continuum half).

## Strategy

For SU(1):

* `IsYangMillsMassProfile` is trivially satisfied: the connected
  correlator vanishes identically (`wilsonConnectedCorr_su1_eq_zero`),
  so the bound `|0| ≤ C · exp(...)` holds with `C := 0`.

* `HasContinuumMassGap_Genuine` is satisfied by the constructive
  `dimensional_transmutation_witness_unconditional` (Phase 17 of
  Cowork session 2026-04-25), which produces a `PhysicalLatticeScheme`
  + `LatticeMassProfile` pair with the genuine continuum-mass-gap
  property via the `trivialPhysicalScheme` + `canonicalAFShape`
  composition.

The two halves use the SAME `m_lat` from the dimensional-transmutation
witness — for SU(1), ANY `m_lat` satisfies `IsYangMillsMassProfile`,
including the canonical-AF-shape one from the continuum side.

## Importance

Predicate hierarchy of unconditional SU(1) witnesses (after this file):

```
                                  N_c = 1 unconditional witness?
ClayYangMillsTheorem                ✓ (trivial existential)
ClayYangMillsMassGap                ✓ (AbelianU1Unconditional, 2026-04-23)
ClayYangMillsPhysicalStrong         ✓ (Phase 43, 2026-04-25)
ClayYangMillsPhysicalStrong_Genuine ✓ Phase 45 — THIS FILE ⭐ (THE STRONGEST)
```

This is the first proof that the project's **strongest currently
defined Clay-grade predicate** has any inhabitant at all.

## Caveats

Per `COWORK_FINDINGS.md`:

* **Finding 003**: SU(1) = `Matrix.specialUnitaryGroup (Fin 1) ℂ` is
  the trivial group `{1}`, NOT abelian QED-like U(1) (which would
  use `unitaryGroup (Fin 1)`).

* **Finding 004**: For SU(1), `HasContinuumMassGap_Genuine` IS
  satisfied via `trivialPhysicalScheme` (which uses real AF-form
  spacing `(1/Λ) · exp(-1/(2 b₀ g²))`), not via the coordinated-scaling
  artifact `latticeSpacing N = 1/(N+1)`. So the "genuine" qualifier
  IS earned at the SU(1) level — but the witness is physics-degenerate
  (no Yang-Mills dynamics).

The witness is therefore **structurally non-vacuous** at the strongest
predicate type, **physics-degenerate** at the Yang-Mills content level.

## Oracle target

Per project discipline, every theorem here should print
`[propext, Classical.choice, Quot.sound]`.

-/

namespace YangMills.Continuum

open Real

/-! ## §1. IsYangMillsMassProfile is trivial for SU(1) -/

/-- For SU(1), `IsYangMillsMassProfile` holds for any `m_lat` with
    constant `C := 0`.

    The proof uses `wilsonConnectedCorr_su1_eq_zero` to reduce the
    LHS to `|0| = 0`, and `0 ≤ 0 * exp(...)` holds trivially. -/
theorem isYangMillsMassProfile_su1_unconditional
    (β : ℝ) (F : ↑(Matrix.specialUnitaryGroup (Fin 1) ℂ) → ℝ)
    (m_lat : LatticeMassProfile) :
    YangMills.IsYangMillsMassProfile
      (sunHaarProb 1) (wilsonPlaquetteEnergy 1) β F
      (fun (N : ℕ) (p q : ConcretePlaquette 4 N) =>
        siteLatticeDist p.site q.site) m_lat := by
  refine ⟨0, le_refl 0, ?_⟩
  intro N _ p q
  rw [wilsonConnectedCorr_su1_eq_zero]
  simp [abs_zero, zero_mul]

#print axioms isYangMillsMassProfile_su1_unconditional

/-! ## §2. ClayYangMillsPhysicalStrong_Genuine for SU(1) — UNCONDITIONAL ⭐⭐ -/

/-- **STRONGEST unconditional inhabitant in the project**:
    `ClayYangMillsPhysicalStrong_Genuine` for SU(1) at the physical
    Clay dimension `d = 4`, with arbitrary `β > 0`, arbitrary
    Wilson observable `F`, and arbitrary positive QCD scale `Λ`.

    Composes:
    1. `dimensional_transmutation_witness_unconditional` (Phase 17,
       Cowork 2026-04-25) — produces `(scheme, m_lat)` with
       `HasContinuumMassGap_Genuine`.
    2. `isYangMillsMassProfile_su1_unconditional` (this file) —
       discharges `IsYangMillsMassProfile` for SU(1) trivially.

    Combining the two halves yields the genuine Clay-grade predicate
    fully unconditionally. -/
theorem clayYangMillsPhysicalStrong_Genuine_su1_unconditional
    (β : ℝ)
    (F : ↑(Matrix.specialUnitaryGroup (Fin 1) ℂ) → ℝ)
    (Λ : ℝ) (hΛ : 0 < Λ) :
    ∃ (scheme : PhysicalLatticeScheme 1),
      ClayYangMillsPhysicalStrong_Genuine
        (sunHaarProb 1) (wilsonPlaquetteEnergy 1) β F
        (fun (N : ℕ) (p q : ConcretePlaquette 4 N) =>
          siteLatticeDist p.site q.site)
        scheme := by
  -- Step 1: get the (scheme, m_lat) pair with HasContinuumMassGap_Genuine.
  obtain ⟨scheme, m_lat, hContinuum⟩ :=
    dimensional_transmutation_witness_unconditional (le_refl 1) Λ hΛ
  refine ⟨scheme, ?_⟩
  -- Step 2: combine IsYangMillsMassProfile (trivial for SU(1))
  -- with HasContinuumMassGap_Genuine (from Phase 17).
  refine ⟨m_lat, ?_, hContinuum⟩
  exact isYangMillsMassProfile_su1_unconditional β F m_lat

#print axioms clayYangMillsPhysicalStrong_Genuine_su1_unconditional

/-! ## §3. Coordination note -/

/-
This file completes the unconditional Clay-grade predicate hierarchy
for SU(1):

| Predicate | Witness location | Date |
|-----------|------------------|------|
| `ClayYangMillsTheorem` | derivable from any of the below | — |
| `ClayYangMillsMassGap 1` | `AbelianU1Unconditional.lean` | 2026-04-23 |
| `ClayYangMillsPhysicalStrong` (1, β, F, ...) | `AbelianU1PhysicalStrongUnconditional.lean` | 2026-04-25 (Phase 43) |
| `ClayYangMillsPhysicalStrong_Genuine` (1, β, F, scheme, ...) | THIS FILE | 2026-04-25 (Phase 45) ⭐ |

Every Clay-grade predicate type in the project is now demonstrably
inhabitable for SU(1). For physically meaningful cases (N_c ≥ 2), the
witness must come from substantive analytic content:
* Codex's F3 chain (Branch I) for `ClayYangMillsMassGap` and
  `ClayYangMillsPhysicalStrong` via small-β cluster expansion.
* Branch III (Cowork RP+TM scaffolds) for independent verification
  at all β.
* Branch II (Bałaban RG, future research-level work) for the
  literal continuum mass gap.
* `dimensional_transmutation_witness_unconditional` already provides
  the genuine continuum half analytically (Phase 17 closure).

Cross-references:
- `AbelianU1Unconditional.lean` — original SU(1) `ClayYangMillsMassGap` witness.
- `AbelianU1PhysicalStrongUnconditional.lean` — Phase 43 `ClayYangMillsPhysicalStrong`.
- `PhysicalSchemeWitness.lean` — `dimensional_transmutation_witness_unconditional`.
- `COWORK_FINDINGS.md` Findings 003 + 004 — caveats.
-/

end YangMills.Continuum
