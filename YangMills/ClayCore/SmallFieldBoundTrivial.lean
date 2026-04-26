/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cowork agent (Claude), under supervision of Lluis Eriksson
-/
import Mathlib
import YangMills.ClayCore.SmallFieldBound

/-!
# Trivial `SmallFieldActivityBound N_c` for arbitrary `N_c`

This module produces an unconditional inhabitant of
`SmallFieldActivityBound N_c` for every `N_c ≥ 1`, completing the
**structural-triviality quartet** with Phases 59, 60, 63.

## Quartet summary (post-Phase 65)

| Phase | Predicate                       | Trivial witness mechanism      |
|-------|---------------------------------|--------------------------------|
| 59    | `BalabanHyps N_c`               | `R := 0` existential           |
| 60    | `WilsonPolymerActivityBound N_c`| `K := 0` universal             |
| 63    | `LargeFieldActivityBound N_c`   | `R := 0` existential + dominance|
| 65    | `SmallFieldActivityBound N_c`   | `activity ≡ 0` universal       |

All four major Bałaban / Branch II **predicate carriers** are now
N_c-agnostically inhabitable with zero/identity witnesses. The
genuine analytic content lives outside the carriers, in the
composition with concrete physical inputs.

## Why `activity := 0` works

The `SmallFieldActivityBound` data type requires:
* `consts : SmallFieldConstants` — positive parameters `(E₀, κ, g)`.
* `activity : ℕ → ℝ` — the activity sequence.
* `hact_nn : ∀ n, 0 ≤ activity n` — nonneg.
* `hact_bd : ∀ n, activity n ≤ E₀ · g² · exp(-κn)` — universal bound.

With `activity := fun _ => 0`:
* `hact_nn n = 0 ≤ 0`. ✓
* `hact_bd n = 0 ≤ E₀ · g² · exp(-κn)`. ✓ (RHS positive)

So the same parameter choice as Phase 59 — `E₀ := 4, κ := 1, g := 1/2` —
yields a clean trivial witness.

## Caveat

Same trivial-group physics-degeneracy of Findings 003 + 011 + 012 +
013 + 014. For `N_c ≥ 2`, the physical small-field activity is
non-trivially exponentially decaying; the trivial witness here is
structurally valid but physics-vacuous.

## Oracle target

`[propext, Classical.choice, Quot.sound]`.

-/

namespace YangMills

open Real

/-! ## §1. Trivial constants -/

/-- Canonical `SmallFieldConstants` matching Phase 59's parameters. -/
noncomputable def trivialSmallFieldConstants : SmallFieldConstants where
  E0 := 4
  hE0 := by norm_num
  kappa := 1
  hkappa := one_pos
  g_bar := 1 / 2
  hg_pos := by norm_num
  hg_lt1 := by norm_num

#print axioms trivialSmallFieldConstants

/-! ## §2. Trivial `SmallFieldActivityBound` -/

/-- **Trivial `SmallFieldActivityBound N_c` for every `N_c ≥ 1`**, with
    `activity ≡ 0` and the canonical small-field constants
    `(E₀ := 4, κ := 1, g := 1/2)`. -/
noncomputable def trivialSmallFieldActivityBound (N_c : ℕ) [NeZero N_c] :
    SmallFieldActivityBound N_c where
  consts := trivialSmallFieldConstants
  activity := fun _ => 0
  hact_nn := fun _ => le_refl 0
  hact_bd := fun n => by
    -- Goal: 0 ≤ 4 * (1/2)² * exp(-1 * n)
    have h1 : (0 : ℝ) ≤ (4 : ℝ) * ((1 : ℝ) / 2) ^ 2 := by norm_num
    exact mul_nonneg h1 (Real.exp_nonneg _)

#print axioms trivialSmallFieldActivityBound

/-! ## §3. SU(1) instantiation -/

/-- The SU(1) instantiation. -/
noncomputable def trivialSmallFieldActivityBound_su1 :
    SmallFieldActivityBound 1 :=
  trivialSmallFieldActivityBound 1

#print axioms trivialSmallFieldActivityBound_su1

/-! ## §4. Coordination note -/

/-
Phase 65 completes the **structural-triviality quartet** in the
Bałaban / Branch II predicate stack. After this phase, **every**
named carrier predicate in the project's Bałaban frontier is
N_c-agnostically inhabitable with a zero / identity / vacuous
witness:

```
SmallFieldActivityBound  ──┐
                           ├── h1_of_small_field_bound ──┐
                           │                              │
WilsonPolymerActivityBound │                              ├── BalabanHyps
                           │                              │
LargeFieldActivityBound  ──┴── h2_of_large_field_bound ──┘
```

Each box is independently trivially inhabitable; the composition
preserves triviality (Phase 61's `balabanHyps_from_trivial_chain`).

## Strategic implication for Branch II at N_c ≥ 2

The structural-triviality observation, taken seriously, says:
"Inhabitation of these predicates is NOT what defines the Bałaban
analytic content." The actual analytic content lives in:

1. The **physical Wilson activity** that the trivial `K` is meant to
   replace.
2. The **physical activity sequence** that the trivial `activity ≡ 0`
   is meant to replace.
3. The **non-trivial existential R-values** in `BalabanHyps` that
   come from honest cluster-expansion estimates.

For `N_c ≥ 2` Clay closure, the path forward is to construct each of
these *physically*, then thread them through Codex's existing
composition machinery (which already correctly handles the
Wilson → small-field / large-field → BalabanHyps chain).

Cross-references:
- `BalabanHypsTrivial.lean` (Phase 59).
- `WilsonPolymerActivityTrivial.lean` (Phase 60).
- `LargeFieldActivityTrivial.lean` (Phase 63).
- `SmallFieldBound.lean` — `SmallFieldActivityBound` definition.
- `COWORK_FINDINGS.md` Findings 013 + 014.
-/

end YangMills
