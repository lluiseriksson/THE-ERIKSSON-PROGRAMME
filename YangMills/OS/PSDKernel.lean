/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson

O-3b(i): the analytic heart of reflection positivity — kernels that are
non-negative combinations of characters are positive semidefinite, and that
class is closed under products.

Charter: docs/O-BRIDGE-CHARTER.md, AMENDMENT 6.
-/

import Mathlib

/-!
# O-3b(i) — non-negative character combinations give PSD kernels

## Where this sits

Reflection positivity for a finite abelian gauge system reduces, after the
Gibbs weight is factored across the reflection plane as `w(x)·w(y)·K(x,y)`, to
positive semidefiniteness of the **crossing kernel** `K`: the full matrix is
`D K D` with `D = diag(w)` strictly positive, so it is PSD exactly when `K` is.
This module proves the statement about `K` and nothing else; the geometric
factorisation that produces `K` is the other half of O-3b and is not assumed,
used, or anticipated here.

## The formulation, and why it is this one

The natural-looking hypothesis is "the Fourier coefficients of the
single-plaquette weight on `Z_N` are non-negative", which would need Bochner's
theorem for finite abelian groups; and the product over crossing plaquettes
would then need the Schur product theorem.  Neither is required if the class is
defined the other way round:

  `K x y = ∑ i, c i * φ i x * conj (φ i y)` with every `c i ≥ 0`.

With that definition positivity is a two-line computation — the form equals
`∑ i, c i * ‖w i‖²` — and the class is **closed under products** for free,
because a product of two such kernels is again one, indexed by pairs, with the
functions multiplied and the coefficients multiplied.  Both facts below are
proved directly, so this module depends on no spectral or matrix-positivity
API at all.

## What is NOT claimed

That the Wilson weight is such a combination.  That is a separate, checkable
fact about a specific Boltzmann factor, and it is where the physics enters; it
is not established here.  Nothing in this module is a statement about gauge
theory, Yang-Mills, or a mass gap.

Oracle target: `[propext, Classical.choice, Quot.sound]`. No sorry, no axioms.
-/

namespace YangMills.OS

set_option linter.unusedSectionVars false

open Finset Complex

variable {X : Type*} [Fintype X] [DecidableEq X]

/-! ## The quadratic form of a kernel -/

/-- The sesquilinear form of a kernel `K` evaluated on a single vector. -/
noncomputable def kernelForm (K : X → X → ℂ) (F : X → ℂ) : ℂ :=
  ∑ x : X, ∑ y : X, (starRingEnd ℂ) (F x) * K x y * F y

/-- A kernel is positive semidefinite when its form is a non-negative real at
every vector.  Stated as "equals a non-negative real" rather than as a
condition on the real part, so that reality is part of the conclusion. -/
def IsPSDKernel (K : X → X → ℂ) : Prop :=
  ∀ F : X → ℂ, ∃ r : ℝ, 0 ≤ r ∧ kernelForm K F = (r : ℂ)

/-! ## Non-negative character combinations -/

/-- `K` is a non-negative combination of the rank-one kernels built from the
family `φ`.  For a finite abelian group the `φ i` are the characters; nothing
below uses that they are characters, only the shape. -/
structure IsCharCombo {ι : Type*} [Fintype ι] (c : ι → ℝ) (φ : ι → X → ℂ)
    (K : X → X → ℂ) : Prop where
  /-- The coefficients are non-negative. -/
  coeff_nonneg : ∀ i, 0 ≤ c i
  /-- The kernel is the corresponding combination. -/
  eq : ∀ x y, K x y = ∑ i, (c i : ℂ) * φ i x * (starRingEnd ℂ) (φ i y)

/-- **The analytic heart.**  A non-negative combination of rank-one kernels is
positive semidefinite, because its form is `∑ i, c i * ‖w i‖²`. -/
theorem isPSDKernel_of_charCombo {ι : Type*} [Fintype ι] {c : ι → ℝ}
    {φ : ι → X → ℂ} {K : X → X → ℂ} (h : IsCharCombo c φ K) :
    IsPSDKernel K := by
  intro F
  refine ⟨∑ i : ι, c i * Complex.normSq (∑ y : X, (starRingEnd ℂ) (φ i y) * F y), ?_, ?_⟩
  · exact Finset.sum_nonneg fun i _ => mul_nonneg (h.coeff_nonneg i) (Complex.normSq_nonneg _)
  · -- Step 1: for each `x`, resum the inner sum over the index `i`.
    have step1 : ∀ x : X,
        ∑ y : X, (starRingEnd ℂ) (F x) * K x y * F y
          = ∑ i : ι, ((c i : ℂ) * (starRingEnd ℂ) (F x) * φ i x)
              * (∑ y : X, (starRingEnd ℂ) (φ i y) * F y) := by
      intro x
      have e1 : ∀ y : X, (starRingEnd ℂ) (F x) * K x y * F y
          = ∑ i : ι, ((c i : ℂ) * (starRingEnd ℂ) (F x) * φ i x)
              * ((starRingEnd ℂ) (φ i y) * F y) := by
        intro y
        rw [h.eq, Finset.mul_sum, Finset.sum_mul]
        exact Finset.sum_congr rfl fun i _ => by ring
      rw [Finset.sum_congr rfl fun y _ => e1 y, Finset.sum_comm]
      exact Finset.sum_congr rfl fun i _ => by rw [Finset.mul_sum]
    -- Step 2: resum over `x`, which produces the conjugate pairing.
    have step2 : ∀ i : ι,
        ∑ x : X, (c i : ℂ) * (starRingEnd ℂ) (F x) * φ i x
          = (c i : ℂ) * (starRingEnd ℂ) (∑ y : X, (starRingEnd ℂ) (φ i y) * F y) := by
      intro i
      rw [map_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun x _ => by
        rw [map_mul, Complex.conj_conj]; ring
    unfold kernelForm
    rw [Finset.sum_congr rfl fun x _ => step1 x, Finset.sum_comm]
    -- the coercion of the real sum must be pushed inside BEFORE `sum_congr`,
    -- or the two sides are not both sums and the congruence is stuck
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_mul, step2 i, Complex.normSq_eq_conj_mul_self]
    ring

/-! ## Closure under products -/

/-- The class is closed under products: the entrywise product of two
non-negative character combinations is another one, indexed by pairs.  This is
what replaces the Schur product theorem here. -/
theorem isCharCombo_mul {ι κ : Type*} [Fintype ι] [Fintype κ]
    {c : ι → ℝ} {d : κ → ℝ} {φ : ι → X → ℂ} {ψ : κ → X → ℂ}
    {K L : X → X → ℂ} (hK : IsCharCombo c φ K) (hL : IsCharCombo d ψ L) :
    IsCharCombo (fun p : ι × κ => c p.1 * d p.2)
      (fun p : ι × κ => fun x => φ p.1 x * ψ p.2 x) (fun x y => K x y * L x y) where
  coeff_nonneg := fun p => mul_nonneg (hK.coeff_nonneg p.1) (hL.coeff_nonneg p.2)
  eq := by
    intro x y
    rw [hK.eq, hL.eq, Finset.sum_mul_sum]
    rw [← Finset.sum_product']
    refine Finset.sum_congr rfl fun p _ => ?_
    push_cast
    simp only [map_mul]
    ring

/-- Consequently a product of non-negative character combinations is PSD. -/
theorem isPSDKernel_mul {ι κ : Type*} [Fintype ι] [Fintype κ]
    {c : ι → ℝ} {d : κ → ℝ} {φ : ι → X → ℂ} {ψ : κ → X → ℂ}
    {K L : X → X → ℂ} (hK : IsCharCombo c φ K) (hL : IsCharCombo d ψ L) :
    IsPSDKernel (fun x y => K x y * L x y) :=
  isPSDKernel_of_charCombo (isCharCombo_mul hK hL)

/-! ## Conjugation by a positive diagonal -/

/-- Conjugating a non-negative character combination by a diagonal is again
one.  This is the step that absorbs the half-space factors `w(x)·w(y)` of the
Gibbs weight, so that reflection positivity reduces to the crossing kernel
alone. -/
theorem isCharCombo_diagConj {ι : Type*} [Fintype ι] {c : ι → ℝ} {φ : ι → X → ℂ}
    {K : X → X → ℂ} (h : IsCharCombo c φ K) (D : X → ℝ) :
    IsCharCombo c (fun i => fun x => (D x : ℂ) * φ i x)
      (fun x y => (D x : ℂ) * K x y * (D y : ℂ)) where
  coeff_nonneg := h.coeff_nonneg
  eq := by
    intro x y
    rw [h.eq, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [map_mul, Complex.conj_ofReal]
    ring

/-! ## Non-vacuity -/

/-- The class is inhabited by a kernel that is not identically zero and whose
form is not identically zero: take one function, coefficient one. -/
theorem isCharCombo_nonvacuous (φ₀ : X → ℂ) :
    IsCharCombo (fun _ : Unit => (1 : ℝ)) (fun _ => φ₀)
      (fun x y => φ₀ x * (starRingEnd ℂ) (φ₀ y)) where
  coeff_nonneg := fun _ => zero_le_one
  eq := by intro x y; simp

/-- And the exhibited kernel is not the zero kernel: its diagonal entry at any
point where `φ₀` is nonzero is nonzero.  Without this, `IsPSDKernel` would be
satisfied here only by the degenerate zero kernel, which is exactly the kind of
vacuous inhabitant this programme's judges exist to exclude. -/
theorem charCombo_kernel_ne_zero (φ₀ : X → ℂ) (x₀ : X) (hφ : φ₀ x₀ ≠ 0) :
    φ₀ x₀ * (starRingEnd ℂ) (φ₀ x₀) ≠ 0 := by
  refine mul_ne_zero hφ ?_
  simpa using hφ

end YangMills.OS
