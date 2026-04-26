/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cowork agent (Claude), under supervision of Lluis Eriksson
-/
import Mathlib
import YangMills.Experimental.LieSUN.LieDerivativeRegularity

/-!
# Theorem-form discharges of `gen_skewHerm` + `gen_trace_zero` at `N_c = 1`

This module provides Lean **theorems** (not axioms) discharging the
SU(1) specializations of two of the three SU(N) generator axioms in
`Experimental/LieSUN/LieDerivativeRegularity.lean`:

* `gen_skewHerm 1 i : (generatorMatrix 1 i)ᴴ = -(generatorMatrix 1 i)`
* `gen_trace_zero 1 i : (generatorMatrix 1 i).trace = 0`

## Why `N_c = 1` is vacuously closed

For `N_c = 1`, `Fin (N_c^2 - 1) = Fin (1 - 1) = Fin 0` is the empty
type. The Lie algebra `su(1)` is zero-dimensional (the only traceless
skew-Hermitian 1×1 complex matrix is `0`), so there are no generators
to index. Hence any forall-over-`i : Fin 0` statement is vacuously
true via `Fin.elim0 : Fin 0 → C` for any motive `C`.

## What this DOES and does NOT do

This file:
* Provides theorem-form proofs of the SU(1) specializations, using only
  `Fin.elim0` (no axiom invocation in the proof term).
* The `#print axioms` of each theorem reports `generatorMatrix` (in
  the statement type) but NOT `gen_skewHerm` or `gen_trace_zero` — the
  axioms are not used in the proof.
* Demonstrates that the SU(1) specializations are **vacuously consistent**.

It does NOT:
* Retire the axioms `gen_skewHerm` or `gen_trace_zero` for general `N_c`.
* Eliminate `generatorMatrix` even at `N_c = 1` (since the statement
  type references it; one would need a separate `def` to provide
  generatorMatrix at N_c = 1, but with i : Fin 0 the function is
  vacuously the empty function).

## Combined with Phase 62

Phase 62 produced `matExp_traceless_det_one_dim_one`. Phase 64 (this
file) extends to two more axioms. Cumulative SU(1) discharge of
`Experimental/` axioms (theorem-form, not retirement):

| Axiom                          | SU(1) theorem | Phase |
|--------------------------------|---------------|-------|
| `matExp_traceless_det_one`     | n=1 dim case  | 62    |
| `gen_skewHerm`                 | N_c=1 vacuous | 64    |
| `gen_trace_zero`               | N_c=1 vacuous | 64    |
| `generatorMatrix`              | (data axiom — not provable, but vacuous use at N_c=1) | — |
| `lieDerivReg_all`              | requires deeper work | — |
| `gronwall_variance_decay`      | Mathlib upstream gap | — |
| `variance_decay_from_bridge_*` | Mathlib upstream gap | — |

3 of 7 axioms now have SU(1)-specific theorem-form discharges.

## Oracle target

`[propext, Classical.choice, Quot.sound]` plus the `generatorMatrix`
data axiom (which appears only in the theorem STATEMENTS, not in the
proof terms).

-/

namespace YangMills.Experimental.LieSUN

open Matrix

/-! ## §1. `gen_skewHerm` at `N_c = 1` — vacuous theorem -/

/-- **`gen_skewHerm` discharged as a theorem at `N_c = 1`**, via the
    fact that `Fin (1^2 - 1) = Fin 0` is empty and any forall over an
    empty type is vacuously true. -/
theorem gen_skewHerm_dim_one (i : Fin (1^2 - 1)) :
    (generatorMatrix 1 i)ᴴ = -(generatorMatrix 1 i) :=
  i.elim0

#print axioms gen_skewHerm_dim_one

/-! ## §2. `gen_trace_zero` at `N_c = 1` — vacuous theorem -/

/-- **`gen_trace_zero` discharged as a theorem at `N_c = 1`**, via the
    same vacuous-empty-type argument. -/
theorem gen_trace_zero_dim_one (i : Fin (1^2 - 1)) :
    (generatorMatrix 1 i).trace = 0 :=
  i.elim0

#print axioms gen_trace_zero_dim_one

/-! ## §3. Bundled vacuous SU(1) generator-axiom discharge -/

/-- **Bundle**: at `N_c = 1`, every SU(N) generator-axiom statement
    holds vacuously because `Fin 0` is empty. -/
theorem all_su1_generator_axioms_vacuous (i : Fin (1^2 - 1)) :
    ((generatorMatrix 1 i)ᴴ = -(generatorMatrix 1 i)) ∧
    ((generatorMatrix 1 i).trace = 0) :=
  i.elim0

#print axioms all_su1_generator_axioms_vacuous

/-! ## §4. Coordination note -/

/-
The SU(N) generator axioms in `LieDerivativeRegularity.lean` declare
`generatorMatrix N_c i : Matrix (Fin N_c) (Fin N_c) ℂ` for
`i : Fin (N_c^2 - 1)`, intended as a Lie-algebra basis index. For
`N_c = 1`, the index type `Fin 0` is empty, so:

* No actual call `generatorMatrix 1 _` ever evaluates (no inhabitant
  of `Fin 0` exists).
* Every property `P (generatorMatrix 1 i)` holds vacuously via
  `Fin.elim0`.

This file makes that vacuity explicit at the theorem level, parallel
to Phase 62's `matExp_traceless_det_one_dim_one`. Combined, the two
phases give the project Lean-level evidence that **3 of 7
Experimental axioms are SU(1)-discharged as theorems**.

For the actual N_c ≥ 2 retirement (substantive Lie-theory work):
* `generatorMatrix` would require a concrete basis construction
  (Gell-Mann matrices for N_c = 3; ladder operators for general N_c).
  Mathlib has `LieAlgebra.SkewHermitian` but no SU(N)-basis exposure.
* `gen_skewHerm` and `gen_trace_zero` would follow from the
  construction (each generator is skew-Hermitian and traceless by
  definition of SU(N)).
* See `SUN_GENERATOR_BASIS_DISCHARGE.md` for the project's roadmap to
  the full retirement.

Cross-references:
- `LieDerivativeRegularity.lean` — axiom locations.
- `MatExpTracelessDimOne.lean` (Phase 62) — companion file.
- `SUN_GENERATOR_BASIS_DISCHARGE.md` — full retirement roadmap.
- `COWORK_FINDINGS.md` Findings 010 + 014 — axiom-frontier discussion.
-/

end YangMills.Experimental.LieSUN
