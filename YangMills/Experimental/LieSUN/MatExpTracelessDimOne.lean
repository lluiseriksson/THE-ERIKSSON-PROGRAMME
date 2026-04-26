/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cowork agent (Claude), under supervision of Lluis Eriksson
-/
import Mathlib
import YangMills.Experimental.LieSUN.LieExpCurve

/-!
# `matExp_traceless_det_one` proved as a theorem at `n = 1`

This module provides a Lean **theorem** (not axiom) discharging the
`n = 1` specialization of the `matExp_traceless_det_one` axiom from
`Experimental/LieSUN/LieExpCurve.lean`.

## Why `n = 1` is tractable without Mathlib's `Matrix.det_exp`

For `n = 1`:
* `Matrix.trace_fin_one : trace A = A 0 0` (Mathlib).
* `Fin 1` is a Subsingleton.
* If `trace X = 0` then `X 0 0 = 0`, hence `X = 0` (matrix-extensionality).
* `(t : ℂ) • 0 = 0` (smul of zero).
* `matExp 0 = 1` (identity matrix; `LieExpCurve.matExp_zero`).
* `det 1 = 1` (`Matrix.det_one`).

So the chain `det (matExp (t • X)) = det (matExp 0) = det 1 = 1`
closes without requiring the `Matrix.det_exp` Mathlib TODO.

## What this does NOT do

This file does **not** retire the `matExp_traceless_det_one` axiom for
the project as a whole. The axiom is universally quantified over `n`,
and the substantive content lives in `n ≥ 2` (where the link
`det (matExp A) = exp (trace A)` requires the matrix-exponential
determinant identity, currently a Mathlib TODO per
`Mathlib/Analysis/Normed/Algebra/MatrixExponential.lean` line 57).

What it does:
* Proves the smallest non-trivial case as a Lean theorem.
* Demonstrates that the axiom is at least consistent at `n = 1`.
* Provides a sanity-check fixture: any future Mathlib-PR retiring the
  axiom for general `n` should agree with this file at `n = 1`.

## Caveat on `n = 0`

The `n = 0` case (`Matrix (Fin 0) (Fin 0) ℂ`) reduces even more
trivially: every matrix is the empty matrix, `det` of the empty matrix
is `1` by Mathlib convention, so the conclusion holds vacuously.
We skip the `n = 0` proof since the project's axiom is implicitly used
at `[NeZero N_c]` constraints elsewhere.

## Oracle target

`[propext, Classical.choice, Quot.sound]`.

-/

namespace YangMills.Experimental.LieSUN

open Matrix

/-! ## §1. Lemma: at `n = 1`, traceless matrices are zero -/

/-- A 1x1 matrix with zero trace is the zero matrix.
    Uses `Matrix.trace_fin_one : trace A = A 0 0` and the fact that
    `Fin 1` has a single element, so the matrix is determined by `A 0 0`. -/
private lemma matrix_fin_one_zero_of_trace_zero
    (X : Matrix (Fin 1) (Fin 1) ℂ) (htr : X.trace = 0) : X = 0 := by
  ext i j
  -- Fin 1 is Subsingleton: i = 0, j = 0
  have hi : i = 0 := Subsingleton.elim i 0
  have hj : j = 0 := Subsingleton.elim j 0
  subst hi; subst hj
  -- Goal: X 0 0 = (0 : Matrix (Fin 1) (Fin 1) ℂ) 0 0 = 0
  have h_entry : X 0 0 = X.trace := (Matrix.trace_fin_one X).symm
  rw [h_entry, htr]
  simp

/-! ## §2. The `n = 1` specialization theorem -/

/-- **`matExp_traceless_det_one` proved as a theorem for `n = 1`.**

    For any `X : Matrix (Fin 1) (Fin 1) ℂ` with `trace X = 0`, and any
    real scalar `t`, `det (matExp (t • X)) = 1`. The proof reduces to
    `det (matExp 0) = det 1 = 1` via `X = 0` (Lemma above) and
    `matExp_zero`. -/
theorem matExp_traceless_det_one_dim_one
    (X : Matrix (Fin 1) (Fin 1) ℂ) (htr : X.trace = 0) (t : ℝ) :
    Matrix.det (matExp ((t : ℂ) • X)) = 1 := by
  -- Step 1: X = 0
  have hX : X = 0 := matrix_fin_one_zero_of_trace_zero X htr
  -- Step 2: t • X = t • 0 = 0
  rw [hX, smul_zero]
  -- Step 3: matExp 0 = 1
  rw [matExp_zero]
  -- Step 4: det 1 = 1
  exact Matrix.det_one

#print axioms matExp_traceless_det_one_dim_one

/-! ## §3. Coordination note -/

/-
This file produces the first **theorem-form** discharge of any
specialization of one of the 7 remaining `Experimental/` axioms. The
specialization is `n = 1`, which is below the SU(N) generator algebra
target (`N_c ≥ 2` would have `Fin (N_c² - 1) = Fin 3, Fin 8, ...`),
but it serves three purposes:

1. **Consistency check**: confirms `matExp_traceless_det_one` is at
   least true at the base case, not vacuously inconsistent.
2. **Mathlib-PR fixture**: when Mathlib eventually closes
   `Matrix.det (NormedSpace.exp A) = NormedSpace.exp (Matrix.trace A)`
   (currently a TODO at `Analysis/Normed/Algebra/MatrixExponential.lean`
   line 57), the resulting general theorem should agree with this file
   at `n = 1`.
3. **Demonstration of the discharge pattern**: the same approach
   (Subsingleton-collapse → matrix is zero → matExp = identity → det = 1)
   does NOT generalize to `n ≥ 2` because traceless does not imply
   zero. So this file makes explicit where the analytic difficulty
   actually starts.

Cross-references:
- `LieExpCurve.lean` — where `matExp_traceless_det_one` is the axiom.
- `Mathlib/Analysis/Normed/Algebra/MatrixExponential.lean` — line 57,
  Matrix-exponential determinant TODO.
- `MATEXP_DET_ONE_DISCHARGE_PROOF.md` — the project's discharge
  roadmap (Phase 29).
- `COWORK_FINDINGS.md` Findings 010 + 014 — axiom-frontier discussion.
-/

end YangMills.Experimental.LieSUN
