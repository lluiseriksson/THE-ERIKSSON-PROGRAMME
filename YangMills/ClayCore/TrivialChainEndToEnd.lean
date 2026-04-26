/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cowork agent (Claude), under supervision of Lluis Eriksson
-/
import Mathlib
import YangMills.ClayCore.WilsonPolymerActivity
import YangMills.ClayCore.WilsonPolymerActivityTrivial
import YangMills.ClayCore.LargeFieldBound
import YangMills.ClayCore.LargeFieldDominance

/-!
# End-to-end trivial chain through `balabanHyps_from_wilson_activity`

This module composes Phase 60's `trivialWilsonPolymerActivityBound`
with a custom-tuned `LargeFieldProfile` to satisfy the dominance
constraint, and threads the result through Codex's actual chain
constructor `balabanHyps_from_wilson_activity` (in
`LargeFieldDominance.lean`) to produce a `BalabanHyps N_c` witness.

## Why this matters

Phase 59 produced `BalabanHyps N_c` directly via `balabanHyps_of_h1_h2`
(skipping the WilsonPolymerActivityBound layer). This file goes the
**full chain** `WilsonPolymerActivityBound → BalabanHyps` via the
intended composition. That demonstrates the structural-triviality
pattern (Findings 013 + 014) holds **end-to-end through Codex's
designed pipeline**, not just at isolated layers.

## Parameter tuning

The dominance constraint
`exp(-profile.eval wab.r) ≤ (wab.A₀ + 1) · wab.r²`
must close. With Phase 60's parameters `A₀ := 1`, `r := 1/2` the
RHS is `2 · (1/2)² = 1/2`. Hence we need
`exp(-profile.eval (1/2)) ≤ 1/2`, i.e.,
`profile.eval (1/2) ≥ log 2 ≈ 0.693`.

We pick `profile.eval := fun _ => 1` (constant 1), which gives
`exp(-1) ≈ 0.368 ≤ 0.5 ✓`. The `heval_pos` requirement
(`0 < eval g`) is satisfied trivially because `1 > 0`.

## Composition shape

```
trivialWilsonPolymerActivityBound (Phase 60)
        ↓
balabanHyps_from_wilson_activity (Codex's actual constructor)
        ↓
BalabanHyps N_c (witness, the same as Phase 59 modulo parameters)
```

This is the **first end-to-end trivial chain witness** in the project
that uses Codex's intended pipeline, not just `balabanHyps_of_h1_h2`.

## Caveat

Same physics-degeneracy of Findings 003 + 011 + 012 + 013 + 014.
The composition is structurally valid; the resulting `BalabanHyps`
carries no Bałaban-RG content because the ingredient
`WilsonPolymerActivityBound` has `K := 0` (Phase 60).

## Oracle target

`[propext, Classical.choice, Quot.sound]`.

-/

namespace YangMills

open Real

/-! ## §1. Custom profile compatible with `trivialWilsonPolymerActivityBound` -/

/-- A trivial `LargeFieldProfile` with `eval ≡ 1` (constant). Always
    positive on `(0, 1)`, so `heval_pos` closes by `one_pos`. -/
noncomputable def trivialLargeFieldProfile : LargeFieldProfile where
  A0 := 1
  hA0 := one_pos
  pstar := 1
  hpstar := one_pos
  eval := fun _ => 1
  heval_pos := fun _ _ _ => one_pos

#print axioms trivialLargeFieldProfile

/-! ## §2. Compatibility with `trivialWilsonPolymerActivityBound` -/

/-- The dominance bound holds for the trivial parameters:
    `exp(-1) ≤ 2 · (1/2)² = 1/2`.
    Via `Real.add_one_le_exp 1 : 1 + 1 = 2 ≤ exp 1`, hence
    `exp(-1) = 1/exp(1) ≤ 1/2`. -/
private lemma trivial_chain_dominance :
    Real.exp (-(1 : ℝ)) ≤ ((1 : ℝ) + 1) * ((1 : ℝ) / 2) ^ 2 := by
  have hRHS : ((1 : ℝ) + 1) * ((1 : ℝ) / 2) ^ 2 = 1 / 2 := by norm_num
  rw [hRHS]
  -- Need exp(-1) ≤ 1/2.
  -- Use Real.add_one_le_exp at x = 1: 2 ≤ exp 1.
  have h_e_ge_2 : (2 : ℝ) ≤ Real.exp 1 := by
    have h := Real.add_one_le_exp (1 : ℝ)
    linarith
  -- Rewrite exp(-1) as 1/exp(1) and apply one_div_le_one_div_of_le.
  rw [Real.exp_neg, ← one_div]
  exact one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) h_e_ge_2

/-! ## §3. End-to-end witness -/

/-- **End-to-end trivial chain witness**: composing Phase 60's
    `trivialWilsonPolymerActivityBound` with `trivialLargeFieldProfile`
    via `balabanHyps_from_wilson_activity` produces a `BalabanHyps N_c`. -/
noncomputable def balabanHyps_from_trivial_chain (N_c : ℕ) [NeZero N_c] :
    BalabanHyps N_c :=
  balabanHyps_from_wilson_activity
    (trivialWilsonPolymerActivityBound N_c)
    trivialLargeFieldProfile
    (fun n => ⟨0, le_refl 0, by
      -- Goal: 0 ≤ exp(-(eval (1/2))) * exp(-(-log (1/2)) * n)
      -- = exp(-1) * exp(log 2 * n)
      -- Both factors positive, so RHS ≥ 0.
      exact mul_nonneg (Real.exp_nonneg _) (Real.exp_nonneg _)⟩)
    trivial_chain_dominance

#print axioms balabanHyps_from_trivial_chain

/-! ## §4. Coordination note -/

/-
This file is a **completeness consequence** of Phases 59 + 60: the
structural-triviality pattern (Findings 013 + 014) does indeed
compose end-to-end through Codex's designed pipeline.

The trivial chain `(K=0, profile=const-1) ⟶ BalabanHyps N_c` is now
verifiable in Lean as a single `noncomputable def`.

Two constructions of `BalabanHyps N_c` now exist in the project:

1. `unconditional_BalabanHyps_trivial` (Phase 59) — direct via
   `balabanHyps_of_h1_h2`.
2. `balabanHyps_from_trivial_chain` (Phase 61, this file) — via
   `balabanHyps_from_wilson_activity`.

Both produce the same `BalabanHyps N_c` shape; both are physics-vacuous
for `N_c ≥ 2` and physics-accurate for SU(1).

For `N_c ≥ 2` Clay closure, the genuine path is to:
* Replace `trivialWilsonPolymerActivityBound` with a non-trivial K
  carrying actual cluster-expansion content.
* Replace `trivialLargeFieldProfile` with the genuine super-polynomial
  profile.
* Discharge `h_lf_bound_at` and `h_dominated` from physical Bałaban-RG
  inputs.

This file is the **trivial-chain skeleton**; the genuine chain has
the same composition shape with non-trivial inputs at every layer.

Cross-references:
- `WilsonPolymerActivityTrivial.lean` (Phase 60) — trivial K source.
- `BalabanHypsTrivial.lean` (Phase 59) — direct construction.
- `LargeFieldDominance.balabanHyps_from_wilson_activity` — the chain
  constructor used here.
- `COWORK_FINDINGS.md` Findings 013 + 014.
-/

end YangMills
