/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lluis Eriksson, Cowork agent (Claude)
-/
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# `det (exp A) = exp (trace A)` for 1×1 complex matrices

This module proves the **`n = 1` case of the Mathlib TODO**

  `Matrix.det (NormedSpace.exp A) = NormedSpace.exp (Matrix.trace A)`

listed at `Mathlib/Analysis/Normed/Algebra/MatrixExponential.lean`
line 57.

The general-`n` case is open (requires Jacobi's formula or Schur
decomposition). This PR closes the smallest non-trivial case as a
stepping stone toward the general result.

## Strategy

For `A : Matrix (Fin 1) (Fin 1) ℂ`:

1. `A = Matrix.diagonal (fun _ => A 0 0)` (any 1×1 matrix is diagonal).
2. `NormedSpace.exp (Matrix.diagonal v) = Matrix.diagonal (NormedSpace.exp ∘ v)`
   (by `Matrix.exp_diagonal` from Mathlib).
3. `Matrix.det (Matrix.diagonal v) = ∏ i, v i` for any function `v`.
4. For `Fin 1`, `∏ i, f i = f 0`.
5. `Matrix.trace A = A 0 0` for `A : Matrix (Fin 1) (Fin 1)`.

Combining: `det (exp A) = exp (A 0 0) = exp (trace A)`.

## PR submission notes

This file has been tested as a direct insertion into
`Mathlib/Analysis/Normed/Algebra/MatrixExponential.lean`, immediately
after `Matrix.exp_diagonal`.

**Status (2026-04-26)**:

1. Built against Mathlib master commit `80a6231dcf`
   (`feat(Analysis/Calculus/Deriv): add deriv_const_mul_id' (#38171)`).
2. `lake build Mathlib.Analysis.Normed.Algebra.MatrixExponential` passed.
3. Full `lake build` in the Mathlib checkout passed.
4. `#print axioms Matrix.det_exp_eq_exp_trace_fin_one` prints
   `[propext, Classical.choice, Quot.sound]`.
5. Local Mathlib branch:
   `C:\Users\lluis\Downloads\mathlib4`, branch
   `eriksson/det-exp-trace-fin-one`, commit `cd3b69baae`.
6. Patch artifact:
   `mathlib_pr_drafts/0001-feat-prove-det-exp-trace-for-1x1-matrices.patch`.

PR submission is blocked only on GitHub publishing setup: this environment
has no `gh` executable, no push permission to upstream Mathlib, and no
reachable fork at `https://github.com/lluiseriksson/mathlib4.git`.
-/

namespace Matrix

open scoped Matrix
open Complex

/-! ## §1. Helper lemma: any 1×1 matrix is diagonal -/

/-- **Any `1 × 1` matrix equals the diagonal of its `(0, 0)` entry.** -/
lemma fin_one_eq_diagonal_zero_zero {α : Type*} [Zero α] [DecidableEq (Fin 1)]
    (A : Matrix (Fin 1) (Fin 1) α) :
    A = Matrix.diagonal (fun _ : Fin 1 => A 0 0) := by
  ext i j
  fin_cases i
  fin_cases j
  simp [Matrix.diagonal]

/-! ## §2. The main theorem -/

/-- **The `n = 1` case of `det (exp A) = exp (trace A)`.**

    This is the smallest non-trivial case of the general
    matrix-exponential determinant identity. The general case is
    a Mathlib TODO at `MatrixExponential.lean:57`. -/
theorem det_exp_eq_exp_trace_fin_one (A : Matrix (Fin 1) (Fin 1) ℂ) :
    det (NormedSpace.exp A) = NormedSpace.exp (trace A) := by
  rw [show A = diagonal (fun _ : Fin 1 => A 0 0) by
    ext i j
    fin_cases i
    fin_cases j
    simp [diagonal]]
  rw [exp_diagonal]
  simp [trace_fin_one, diagonal]

#print axioms Matrix.det_exp_eq_exp_trace_fin_one

end Matrix
