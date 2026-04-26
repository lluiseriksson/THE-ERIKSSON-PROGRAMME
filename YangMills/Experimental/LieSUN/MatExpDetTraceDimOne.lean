/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cowork agent (Claude), under supervision of Lluis Eriksson
-/
import Mathlib
import YangMills.Experimental.LieSUN.LieExpCurve

/-!
# `det (matExp A) = exp (trace A)` proved at `n = 1`

This module proves the **`n = 1` case of the Mathlib TODO**:

> `Matrix.det (NormedSpace.exp A) = NormedSpace.exp (Matrix.trace A)`

(listed at `Mathlib/Analysis/Normed/Algebra/MatrixExponential.lean`
line 57).

## Strategy

For `n = 1`:

1. Every `A : Matrix (Fin 1) (Fin 1) ℂ` is the diagonal of its
   `(0,0)`-entry: `A = Matrix.diagonal (fun _ => A 0 0)`.
2. By `Matrix.exp_diagonal`,
   `exp (diagonal v) = diagonal (exp v)`.
3. By `Matrix.det_diagonal`, `det (diagonal v) = ∏ i, v i = v 0`
   (since `Fin 1` has one element).
4. By `Matrix.trace_fin_one`, `trace A = A 0 0`.

Combining: `det (matExp A) = det (exp (diagonal (fun _ => A 0 0))) =
det (diagonal (fun _ => exp (A 0 0))) = exp (A 0 0) = exp (trace A)`.

## Strategic value

This file:

* Closes the smallest non-trivial case (`n = 1`) of the Mathlib TODO.
* Provides a **template** for future generalisation to `n ≥ 2`,
  which requires diagonalisability / Schur decomposition + the
  multiplicativity of `det` and additivity of `trace` on
  similar matrices.
* Combined with Phase 62's `matExp_traceless_det_one_dim_one`, gives
  Cowork's strongest evidence that the `matExp_traceless_det_one`
  axiom is at minimum self-consistent at the base case.

## What this does NOT do

* Does NOT retire the global axiom `matExp_traceless_det_one` for
  `n ≥ 2`. That requires the full Mathlib TODO (Schur / Cayley-
  Hamilton / Jacobi formula).
* Does NOT specialize to traceless matrices (Phase 62 does that
  separately for the `matExp_traceless_det_one` axiom statement).

## Oracle target

`[propext, Classical.choice, Quot.sound]`.

-/

namespace YangMills.Experimental.LieSUN

open Matrix Complex

/-! ## §1. Helper: every 1x1 matrix is diagonal -/

/-- A 1x1 matrix is the diagonal of its `(0,0)`-entry. -/
private lemma matrix_fin_one_eq_diagonal (A : Matrix (Fin 1) (Fin 1) ℂ) :
    A = Matrix.diagonal (fun _ => A 0 0) := by
  ext i j
  have hi : i = 0 := Subsingleton.elim i 0
  have hj : j = 0 := Subsingleton.elim j 0
  subst hi; subst hj
  simp [Matrix.diagonal]

/-! ## §2. Main: det (matExp A) = Complex.exp (trace A) at n = 1 -/

/-- **`det (matExp A) = exp (trace A)` proved at `n = 1`.**

    Combines `Matrix.exp_diagonal` (after recasting A as a diagonal),
    `Matrix.det_diagonal` (to extract the single entry), and
    `Matrix.trace_fin_one` (to identify `trace A` with `A 0 0`).

    The proof routes through `NormedSpace.exp ℂ` (which is
    `matExp` in this project), so it directly addresses the
    Mathlib TODO at `MatrixExponential.lean` line 57. -/
theorem matExp_det_eq_exp_trace_dim_one
    (A : Matrix (Fin 1) (Fin 1) ℂ) :
    Matrix.det (matExp A) = Complex.exp (Matrix.trace A) := by
  -- Step 1: A = diagonal (fun _ => A 0 0)
  have hA_diag : A = Matrix.diagonal (fun _ => A 0 0) :=
    matrix_fin_one_eq_diagonal A
  -- Step 2: trace A = A 0 0
  have h_trace : Matrix.trace A = A 0 0 := Matrix.trace_fin_one A
  -- Step 3: matExp (diagonal v) = diagonal (exp v) (Matrix.exp_diagonal)
  -- We need `matExp` to be defeq to `Matrix.exp` (the one with Algebra ℚ).
  -- In our project `matExp = NormedSpace.exp ℂ`, which equals
  -- `Matrix.exp ℂ` (the public version) on ℂ-matrices.
  -- For n = 1 with explicit value, the chain reduces.
  rw [hA_diag, h_trace]
  -- Goal: det (matExp (diagonal (fun _ => A 0 0))) = exp (A 0 0)
  -- Replace matExp with its definition NormedSpace.exp _,
  -- and apply exp_diagonal + det_diagonal.
  show Matrix.det
    (@NormedSpace.exp ℂ (Matrix (Fin 1) (Fin 1) ℂ) _ (topRingMat 1)
      (Matrix.diagonal (fun _ => A 0 0))) =
    Complex.exp (A 0 0)
  -- The exp_diagonal lemma is for Matrix.exp (NOT NormedSpace.exp).
  -- Both are equal on n × n matrices over a normed Q-algebra.
  -- So we use it via a rewrite through the equality.
  -- For ℂ (which has Algebra ℚ), Matrix.exp_diagonal applies.
  rw [show (@NormedSpace.exp ℂ (Matrix (Fin 1) (Fin 1) ℂ) _ (topRingMat 1)
        (Matrix.diagonal (fun _ : Fin 1 => A 0 0))) =
      Matrix.diagonal (fun _ : Fin 1 => Complex.exp (A 0 0)) from by
    exact Matrix.exp_diagonal (𝔸 := ℂ) (fun _ => A 0 0)]
  -- Goal: det (diagonal (fun _ => Complex.exp (A 0 0))) = Complex.exp (A 0 0)
  rw [Matrix.det_diagonal]
  -- Goal: ∏ i : Fin 1, Complex.exp (A 0 0) = Complex.exp (A 0 0)
  simp

#print axioms matExp_det_eq_exp_trace_dim_one

/-! ## §3. Corollary: traceless case recovers `matExp_traceless_det_one_dim_one` -/

/-- **Corollary**: if `trace A = 0`, then `det (matExp (t • A)) = 1`.

    Combines `matExp_det_eq_exp_trace_dim_one` with
    `Complex.exp_zero = 1`.

    This recovers `matExp_traceless_det_one_dim_one` (Phase 62) via
    the more general identity. -/
theorem matExp_smul_traceless_det_eq_one_dim_one
    (A : Matrix (Fin 1) (Fin 1) ℂ) (htr : Matrix.trace A = 0) (t : ℝ) :
    Matrix.det (matExp ((t : ℂ) • A)) = 1 := by
  -- For n = 1, traceless ⇒ A = 0 ⇒ t • A = 0 ⇒ matExp 0 = 1 ⇒ det 1 = 1
  -- Alternative via the more general identity:
  -- det (matExp (t • A)) = exp (trace (t • A)) = exp (t * trace A) = exp 0 = 1
  rw [matExp_det_eq_exp_trace_dim_one]
  -- Goal: Complex.exp (trace (t • A)) = 1
  rw [Matrix.trace_smul, htr]
  -- Goal: Complex.exp ((t : ℂ) • (0 : ℂ)) = 1
  simp

#print axioms matExp_smul_traceless_det_eq_one_dim_one

/-! ## §4. Coordination note -/

/-
This file is the most concrete contribution toward retiring the
`matExp_traceless_det_one` axiom (one of the 7 Experimental axioms).
The general theorem `matExp_det_eq_exp_trace` for arbitrary `n` is
the Mathlib TODO at `Analysis/Normed/Algebra/MatrixExponential.lean`
line 57. This file closes the `n = 1` base case directly.

Future work to fully retire `matExp_traceless_det_one`:

1. **Mathlib upstream**: prove `Matrix.det (NormedSpace.exp A) =
   NormedSpace.exp (Matrix.trace A)` for arbitrary `n`. The standard
   argument is via Schur decomposition (every complex matrix is
   similar to an upper-triangular one), then multiplicativity of
   `det` and the diagonal nature of trace under triangularisation.
2. **Project-side**: once Mathlib has the theorem, replace
   `matExp_traceless_det_one` with a direct corollary.

Cross-references:
- `LieExpCurve.lean` — `matExp` definition + the axiom statement.
- `MatExpTracelessDimOne.lean` (Phase 62) — companion proof of the
  axiom-shape for `n = 1`.
- `Mathlib/Analysis/Normed/Algebra/MatrixExponential.lean` — the
  TODO.
- `MATEXP_DET_ONE_DISCHARGE_PROOF.md` — full retirement roadmap.
- `COWORK_FINDINGS.md` Findings 010 + 014 — axiom-frontier
  discussion.
-/

end YangMills.Experimental.LieSUN
