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

  `Matrix.det (NormedSpace.exp ℂ A) = Complex.exp (Matrix.trace A)`

listed at `Mathlib/Analysis/Normed/Algebra/MatrixExponential.lean`
line 57.

The general-`n` case is open (requires Jacobi's formula or Schur
decomposition). This PR closes the smallest non-trivial case as a
stepping stone toward the general result.

## Strategy

For `A : Matrix (Fin 1) (Fin 1) ℂ`:

1. `A = Matrix.diagonal (fun _ => A 0 0)` (any 1×1 matrix is diagonal).
2. `NormedSpace.exp ℂ (Matrix.diagonal v) = Matrix.diagonal (Complex.exp ∘ v)`
   (by `Matrix.exp_diagonal` from Mathlib).
3. `Matrix.det (Matrix.diagonal v) = ∏ i, v i` for any function `v`.
4. For `Fin 1`, `∏ i, f i = f 0`.
5. `Matrix.trace A = A 0 0` for `A : Matrix (Fin 1) (Fin 1)`.

Combining: `det (exp A) = exp (A 0 0) = exp (trace A)`.

## PR submission notes

This file is suitable for direct submission to Mathlib at
`Mathlib/Analysis/Normed/Algebra/MatrixExponential.lean`. It uses
only standard Mathlib imports. The exact form of `Matrix.exp_diagonal`
and the corresponding Mathlib API names should be verified against
the current Mathlib master branch before submission.

**Status (2026-04-25)**: this file was produced in the workspace
but has NOT been built with `lake build`. It is a polished
PR-ready candidate that requires:
1. `lake build` to type-check on Mathlib master.
2. PR description in `mathlib_pr_drafts/PR_DESCRIPTION.md`.
3. Mathlib contribution-guidelines compliance check.
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
    Matrix.det (NormedSpace.exp ℂ A) = Complex.exp (Matrix.trace A) := by
  -- Rewrite A as diagonal.
  have h_A : A = Matrix.diagonal (fun _ : Fin 1 => A 0 0) :=
    fin_one_eq_diagonal_zero_zero A
  -- Compute trace = A 0 0 (using Matrix.trace_fin_one).
  have h_trace : Matrix.trace A = A 0 0 := Matrix.trace_fin_one A
  -- Goal: det (exp A) = exp (A 0 0).
  rw [h_trace, h_A]
  -- exp of diagonal is diagonal of exp componentwise.
  rw [Matrix.exp_diagonal]
  -- det of 1×1 diagonal is the single entry.
  rw [Matrix.det_fin_one]
  -- The (0, 0) entry of the diagonal is the value at 0.
  simp [Matrix.diagonal]

end Matrix
