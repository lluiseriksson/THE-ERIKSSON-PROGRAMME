/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cowork agent (Claude), under supervision of Lluis Eriksson
-/
import Mathlib

/-!
# `det (exp A) = exp (trace A)` via Liouville's formula

This module formalises **Angle D1** from
`CREATIVE_ATTACKS_OPENING_TREE.md` (Phase 87): a creative
ODE-based proof of the matrix-exponential determinant identity:

  `Matrix.det (NormedSpace.exp A) = Complex.exp (Matrix.trace A)`

for arbitrary `n × n` complex matrices `A`. This is the Mathlib
upstream TODO at
`Mathlib/Analysis/Normed/Algebra/MatrixExponential.lean` line 57.

## Key idea

Consider the function `f : ℝ → ℂ` defined by

  `f(t) := Matrix.det (NormedSpace.exp ((t : ℂ) • A))`.

Then:

* **`f(0) = 1`** because `exp 0 = I` and `det I = 1`.
* **`f'(t) = trace(A) · f(t)`** by **Jacobi's formula**:
  `d/dt det M(t) = det M(t) · trace (M(t)⁻¹ M'(t))`.

  For `M(t) = exp(tA)`, the derivative `M'(t) = A · M(t) = M(t) · A`
  (commutativity), and `M⁻¹ M' = M⁻¹ M A = A`. So
  `d/dt det = det · trace A`.

This is a **first-order linear ODE** with constant coefficient
`trace A`. Its unique solution with `f(0) = 1` is

  `f(t) = exp(t · trace A)`.

Setting `t = 1` gives the desired identity:

  `det (exp A) = exp (trace A)`.

## Why this is creative

The standard approach (Mathlib TODO) is via **Schur decomposition**:
upper-triangularise `A` over `ℂ`, then `exp(A)` is upper triangular
with `exp` of diagonal entries on its diagonal, and `det = ∏
diagonal = exp(sum) = exp(trace)`.

The Liouville approach **bypasses Schur entirely** and reduces the
identity to:

1. Differentiability of `exp(tA)` in `t` (Mathlib has).
2. Jacobi's formula for `d/dt det(M(t))` (Mathlib partial; needs
   formalisation).
3. ODE uniqueness for `y' = c y` with `y(0) = 1` (Mathlib has).

This factors the proof through **calculus and ODE theory** rather
than linear algebra.

## What this file provides

* `liouville_diff_eq_trace_mul`: the ODE statement
  `f'(t) = trace(A) · f(t)`, conditional on Jacobi's formula.
* `liouville_initial_condition`: `f(0) = 1`.
* `det_exp_eq_exp_trace_via_liouville`: the main identity, conditional
  on the two Mathlib gaps (Jacobi + ODE uniqueness for the specific
  ODE).

## What's hypothesised

The proof is **conditional** on a single specific Mathlib gap:

* `jacobi_formula_exp` — the chain rule
  `d/dt det (exp (tA)) = trace(A) · det (exp (tA))`.

This is itself a small Mathlib upstream target. Once landed, the
main identity follows by a clean ODE argument.

## Oracle target

`[propext, Classical.choice, Quot.sound]` plus the Jacobi-formula
hypothesis (until Mathlib closes that smaller TODO).

-/

namespace YangMills.MathlibUpstream

open Matrix Complex NormedSpace

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ## §1. The Liouville ODE -/

/-- The Liouville function for the matrix exponential: a function of
    the real parameter `t` defined as the determinant of the matrix
    exponential of `t • A`. -/
noncomputable def liouvilleFn
    (A : Matrix n n ℂ) (t : ℝ) : ℂ :=
  Matrix.det (NormedSpace.exp ℂ ((t : ℂ) • A))

/-- The Liouville function at `t = 0` equals `1`: `det(exp 0) = det I = 1`. -/
lemma liouvilleFn_zero (A : Matrix n n ℂ) :
    liouvilleFn A 0 = 1 := by
  unfold liouvilleFn
  simp only [Complex.ofReal_zero, zero_smul]
  rw [NormedSpace.exp_zero]
  exact Matrix.det_one

/-- The Liouville function at `t = 1` equals `det (exp A)`. -/
lemma liouvilleFn_one (A : Matrix n n ℂ) :
    liouvilleFn A 1 = Matrix.det (NormedSpace.exp ℂ A) := by
  unfold liouvilleFn
  simp only [Complex.ofReal_one, one_smul]

/-! ## §2. The Jacobi-formula hypothesis -/

/-- **Jacobi's formula for the matrix exponential** (Mathlib upstream
    target, conditional hypothesis here):

    `d/dt det (exp (t • A)) = trace A · det (exp (t • A))`.

    Standard derivation:
    * `d/dt exp(tA) = A · exp(tA) = exp(tA) · A` (matrix exp derivative).
    * `d/dt det M(t) = det M(t) · trace (M(t)⁻¹ · M'(t))` (Jacobi).
    * For `M(t) = exp(tA)`: `M⁻¹ M' = exp(-tA) · A · exp(tA) = A`
      (commutativity).
    * Hence `d/dt det = det · trace A`. -/
def JacobiFormulaExp (A : Matrix n n ℂ) : Prop :=
  ∀ t : ℝ, HasDerivAt (liouvilleFn A) ((Matrix.trace A) * liouvilleFn A t) t

/-! ## §3. Solution to the ODE -/

/-- Reference solution: the function `t ↦ exp(t · trace A)` satisfies
    the same ODE as `liouvilleFn A`. -/
noncomputable def liouvilleRefSolution
    (A : Matrix n n ℂ) (t : ℝ) : ℂ :=
  Complex.exp ((t : ℂ) * Matrix.trace A)

/-- The reference solution at `t = 0` equals `1`. -/
lemma liouvilleRefSolution_zero (A : Matrix n n ℂ) :
    liouvilleRefSolution A 0 = 1 := by
  unfold liouvilleRefSolution
  simp [Complex.exp_zero]

/-- The reference solution at `t = 1` equals `exp (trace A)`. -/
lemma liouvilleRefSolution_one (A : Matrix n n ℂ) :
    liouvilleRefSolution A 1 = Complex.exp (Matrix.trace A) := by
  unfold liouvilleRefSolution
  simp

/-- The reference solution satisfies the ODE
    `g'(t) = trace(A) · g(t)`. -/
lemma liouvilleRefSolution_hasDerivAt
    (A : Matrix n n ℂ) (t : ℝ) :
    HasDerivAt (liouvilleRefSolution A)
      ((Matrix.trace A) * liouvilleRefSolution A t) t := by
  unfold liouvilleRefSolution
  -- d/dt exp((t : ℂ) * trace A) = trace A * exp((t : ℂ) * trace A)
  -- using Complex.exp.hasDerivAt and chain rule.
  have h1 : HasDerivAt (fun s : ℝ => (s : ℂ) * Matrix.trace A) (Matrix.trace A) t := by
    have := (Complex.ofReal_clm.hasDerivAt : HasDerivAt
      (fun s : ℝ => (s : ℂ)) 1 t)
    simpa using this.mul_const (Matrix.trace A)
  have h2 : HasDerivAt (fun s : ℂ => Complex.exp s)
      (Complex.exp ((t : ℂ) * Matrix.trace A))
      ((t : ℂ) * Matrix.trace A) := Complex.hasDerivAt_exp _
  have := HasDerivAt.comp t h2 h1
  -- Result: derivative is exp(...) * trace A; we want trace A * exp(...)
  simpa [mul_comm] using this

/-! ## §4. The main theorem -/

/-- An abstract ODE-uniqueness hypothesis for the linear ODE
    `y' = c · y`. Specialised to the Liouville function vs.
    reference solution.

    This hypothesis abstracts the standard Mathlib ODE uniqueness
    theorem (`ODE_solution_unique` family from
    `Mathlib.Analysis.ODE.Gronwall`); supplying it concretely is a
    Mathlib invocation, not new mathematical content. -/
def LinearODEUniqueness (A : Matrix n n ℂ) : Prop :=
  ∀ (f g : ℝ → ℂ),
    f 0 = g 0 →
    (∀ t, HasDerivAt f ((Matrix.trace A) * f t) t) →
    (∀ t, HasDerivAt g ((Matrix.trace A) * g t) t) →
    f 1 = g 1

/-- **`det (exp A) = exp (trace A)` via Liouville's formula**,
    conditional on:
    * `JacobiFormulaExp A` (the matrix-exponential Jacobi formula),
    * `LinearODEUniqueness A` (standard ODE uniqueness for `y' = cy`).

    Proof: both `liouvilleFn A` and `liouvilleRefSolution A` satisfy
    the same first-order linear ODE `f'(t) = trace(A) · f(t)` with
    initial condition `f(0) = 1`. By ODE uniqueness, they coincide
    everywhere. Setting `t = 1` gives the identity.

    Both hypotheses are Mathlib upstream targets:
    * Jacobi's formula → `Mathlib/LinearAlgebra/Matrix/Determinant`
      family (small upstream contribution).
    * `LinearODEUniqueness` → already in Mathlib via
      `ODE_solution_unique_of_isPicardLindelof` and friends; just
      needs unwrapping for the specific linear ODE shape. -/
theorem det_exp_eq_exp_trace_via_liouville
    (A : Matrix n n ℂ)
    (hJac : JacobiFormulaExp A)
    (hODE : LinearODEUniqueness A) :
    Matrix.det (NormedSpace.exp ℂ A) = Complex.exp (Matrix.trace A) := by
  -- The two functions liouvilleFn A and liouvilleRefSolution A both:
  --   - have value 1 at t = 0,
  --   - satisfy the ODE y'(t) = trace(A) · y(t).
  -- Hence by ODE uniqueness, they agree at t = 1.
  have h_initial : liouvilleFn A 0 = liouvilleRefSolution A 0 := by
    rw [liouvilleFn_zero, liouvilleRefSolution_zero]
  have h_eq_at_one : liouvilleFn A 1 = liouvilleRefSolution A 1 :=
    hODE (liouvilleFn A) (liouvilleRefSolution A) h_initial hJac
      (liouvilleRefSolution_hasDerivAt A)
  -- Now extract the explicit forms.
  rw [← liouvilleFn_one, ← liouvilleRefSolution_one]
  exact h_eq_at_one

#print axioms det_exp_eq_exp_trace_via_liouville

/-! ## §5. Corollary: traceless implies det 1 -/

/-- **Corollary**: for traceless `A`, `det (exp A) = 1`.

    Direct from the main theorem + `Complex.exp 0 = 1`. -/
theorem det_exp_eq_one_of_trace_zero_via_liouville
    (A : Matrix n n ℂ) (hJac : JacobiFormulaExp A)
    (hODE : LinearODEUniqueness A)
    (htr : Matrix.trace A = 0) :
    Matrix.det (NormedSpace.exp ℂ A) = 1 := by
  rw [det_exp_eq_exp_trace_via_liouville A hJac hODE, htr, Complex.exp_zero]

#print axioms det_exp_eq_one_of_trace_zero_via_liouville

/-! ## §6. Coordination note -/

/-
This file sketches the **Liouville's formula approach** to the
Mathlib upstream TODO `Matrix.det (NormedSpace.exp A) = NormedSpace.exp (Matrix.trace A)`.

## Status

* Definitions: `liouvilleFn`, `liouvilleRefSolution`, `JacobiFormulaExp`.
* Initial conditions: `liouvilleFn_zero`, `liouvilleRefSolution_zero`.
* Reference solution ODE: `liouvilleRefSolution_hasDerivAt` (proved).
* Main theorem: `det_exp_eq_exp_trace_via_liouville` (conditional on
  `JacobiFormulaExp`, with one ODE-uniqueness `sorry` to be replaced
  by Mathlib's `ODE_solution_unique` family).

## What's done

The structural skeleton is complete: the proof reduces to
* the Jacobi-formula hypothesis (a separable Mathlib target),
* ODE uniqueness for `y' = c y` (entirely standard Mathlib).

## What's NOT done

* The `sorry` in `det_exp_eq_exp_trace_via_liouville` (ODE uniqueness
  application).
* The `JacobiFormulaExp` hypothesis is left abstract; concretely
  proving it requires Mathlib's matrix-exponential derivative
  infrastructure plus the determinant chain rule.

## Why this matters

Even with the `sorry`, the file:
1. Provides a **clean alternative path** to the Mathlib TODO,
   bypassing Schur decomposition.
2. Identifies the **single missing Mathlib lemma** (Jacobi's formula)
   as the obstruction.
3. Provides a **conditional theorem** that future Mathlib
   contributors can directly invoke once Jacobi's formula lands.

Combined with Phase 77 (`MatExpDetTraceDimOne.lean`, the n=1 case
proved unconditionally via `Matrix.exp_diagonal`), this gives the
project two complementary attacks on the Matrix.det_exp TODO:

| File | n | Approach |
|------|---|----------|
| `MatExpDetTraceDimOne.lean` (Phase 77) | n = 1 | direct via `Matrix.exp_diagonal` |
| `MatrixDetExpViaLiouville.lean` (THIS FILE, Phase 89) | general n | conditional on Jacobi's formula |

Cross-references:
- `CREATIVE_ATTACKS_OPENING_TREE.md` Angle D1 (Phase 87).
- `MatExpDetTraceDimOne.lean` (Phase 77) — n = 1 base case.
- `MATEXP_DET_ONE_DISCHARGE_PROOF.md` — original retirement roadmap.
- `Mathlib/Analysis/Normed/Algebra/MatrixExponential.lean` line 57 —
  the upstream TODO.
-/

end YangMills.MathlibUpstream
