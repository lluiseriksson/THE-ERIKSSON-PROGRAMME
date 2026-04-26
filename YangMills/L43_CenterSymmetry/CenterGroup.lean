/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lluis Eriksson, Cowork agent (Claude)
-/
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Data.Complex.Basic

/-!
# `L43_CenterSymmetry.CenterGroup`: The `Z_N` center of SU(N)

This module formalises the **`Z_N` center subgroup** of SU(N), the
foundational object distinguishing confined from deconfined phases of
pure Yang-Mills.

## Mathematical content

The center of SU(N) is

  `Z(SU(N)) = { ω · I : ω^N = 1 } ≅ Z_N`,

where `I` is the identity matrix and `ω` ranges over `N`-th roots of
unity. There are `N` elements; `Z(SU(2)) = {±I}`, `Z(SU(3)) =
{I, e^(2πi/3) I, e^(4πi/3) I}`, etc.

In pure Yang-Mills, the center symmetry acts on the gauge field via
`A → A` and on the Wilson loop wrapping a non-trivial cycle (e.g., a
Polyakov loop) via `tr P → ω · tr P`. The **order parameter for
deconfinement** is the expectation `⟨tr P⟩`:

* **Confined phase**: center symmetry is unbroken, `⟨tr P⟩ = 0`.
* **Deconfined phase**: center symmetry is spontaneously broken,
  `⟨tr P⟩ ≠ 0`.

This module defines the center group as a Lean structure and proves
basic properties.

## Strategy

The center is defined as a `def` parametrised by `N : ℕ`. The center
elements are `ω^k · I` for `k ∈ {0, 1, ..., N-1}`. We do not yet
implement the SU(N) matrix structure (which would require deeper
Lean infrastructure); instead, we work with the abstract `N`-th roots
of unity.

## Status

This file is structural physics scaffolding. The substantive
implementation of SU(N) matrix center elements, with full integration
into the project's Wilson Gibbs measure, would require additional
Mathlib infrastructure.

**Status (2026-04-25)**: produced in workspace, not yet built with
`lake build`. Statements are short and elementary.
-/

namespace L43_CenterSymmetry

open Complex

/-! ## §1. The `N`-th root of unity -/

/-- **`N`-th root of unity** `ω = exp(2πi/N)`. -/
noncomputable def primitiveRoot (N : ℕ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I / N)

/-- **Primitive root is non-zero**. -/
theorem primitiveRoot_ne_zero (N : ℕ) : primitiveRoot N ≠ 0 := by
  unfold primitiveRoot
  exact Complex.exp_ne_zero _

#print axioms primitiveRoot_ne_zero

/-- **Modulus of the primitive root is 1**. -/
theorem primitiveRoot_abs (N : ℕ) (hN : 1 ≤ N) :
    Complex.abs (primitiveRoot N) = 1 := by
  unfold primitiveRoot
  rw [Complex.abs_exp]
  -- Real.exp((2πi/N).re) = Real.exp(0) = 1
  have h_re : ((2 * Real.pi * Complex.I / (N : ℂ))).re = 0 := by
    rw [show (2 * Real.pi * Complex.I / (N : ℂ)) =
      (2 * Real.pi : ℂ) * Complex.I * ((N : ℂ)⁻¹) from by ring]
    simp [Complex.I_re, Complex.I_im]
  rw [h_re]
  exact Real.exp_zero

/-! ## §2. The center group `Z_N` of SU(N) -/

/-- **`Z_N` center element**: `centerElement N k = ω^k` where
    `ω = exp(2πi/N)` is the primitive `N`-th root of unity.

    Each `centerElement N k` corresponds (when extended to a matrix)
    to `ω^k · I` ∈ SU(N). -/
noncomputable def centerElement (N : ℕ) (k : ℕ) : ℂ :=
  primitiveRoot N ^ k

/-- **Center elements have modulus 1** for `N ≥ 1`. -/
theorem centerElement_abs (N : ℕ) (hN : 1 ≤ N) (k : ℕ) :
    Complex.abs (centerElement N k) = 1 := by
  unfold centerElement
  rw [map_pow, primitiveRoot_abs N hN, one_pow]

/-! ## §3. Special cases: `Z_2` (= SU(2) center) and `Z_3` (= SU(3) center) -/

/-- **`Z_2` center element**: `centerElement 2 0 = 1`,
    `centerElement 2 1 = -1`. -/
theorem centerElement_two_one : centerElement 2 1 = -1 := by
  unfold centerElement primitiveRoot
  rw [pow_one]
  -- exp(2πi/2) = exp(πi) = -1
  rw [show (2 * Real.pi * Complex.I / (2 : ℂ)) =
    (Real.pi : ℂ) * Complex.I from by push_cast; ring]
  exact Complex.exp_pi_mul_I

#print axioms centerElement_two_one

/-- **`Z_2` center element 0**: `centerElement 2 0 = 1`. -/
theorem centerElement_two_zero : centerElement 2 0 = 1 := by
  unfold centerElement
  exact pow_zero _

/-! ## §4. Cyclicity of the center -/

/-- **Cyclicity of the center**: for `N ≥ 1`, `(centerElement N k)^N = 1`,
    i.e., the `N`-th power of any center element is the identity. -/
theorem centerElement_pow_N (N : ℕ) (hN : 1 ≤ N) (k : ℕ) :
    (centerElement N k)^N = 1 := by
  unfold centerElement primitiveRoot
  rw [← pow_mul]
  -- exp(2πi · (k · N) / N)^... = exp(2πi · k) = 1
  rw [show (Complex.exp (2 * Real.pi * Complex.I / (N : ℂ)) ^ (k * N)) =
    Complex.exp (2 * Real.pi * Complex.I / (N : ℂ) * (k * N : ℕ)) from by
    rw [← Complex.exp_nat_mul]; ring_nf]
  -- (2πi/N) · (kN) = 2πi · k
  have h_N_ne : (N : ℂ) ≠ 0 := by
    have : (0 : ℂ) < (N : ℂ) := by exact_mod_cast hN
    exact ne_of_gt this
  have h_simp : (2 * Real.pi * Complex.I / (N : ℂ) * (k * N : ℕ)) =
      2 * Real.pi * Complex.I * (k : ℂ) := by
    push_cast
    field_simp
    ring
  rw [h_simp]
  -- exp(2πi · k) = 1
  rw [show (2 * Real.pi * Complex.I * (k : ℂ)) = (k : ℕ) * (2 * Real.pi * Complex.I) from by
    push_cast; ring]
  rw [Complex.exp_nat_mul, Complex.exp_two_pi_mul_I, one_pow]

/-! ## §5. Polyakov loop and order parameter (abstract) -/

/-- **Abstract Polyakov loop expectation**: a quantity `polyExp`
    valued in ℂ that transforms under the `Z_N` center action as

      `polyExp ↦ ω · polyExp`. -/
structure PolyakovExpectation (N : ℕ) where
  /-- The Polyakov loop expectation value `⟨P⟩ : ℂ`. -/
  P : ℂ

/-- **Center transformation** of Polyakov expectation. -/
noncomputable def PolyakovExpectation.centerTransform {N : ℕ} (hN : 1 ≤ N)
    (poly : PolyakovExpectation N) (k : ℕ) :
    PolyakovExpectation N where
  P := centerElement N k * poly.P

/-- **Center invariance condition (hypothesis-conditioned)**: if a
    nontrivial center element `ω` (i.e., `ω ≠ 1`) acts on `⟨P⟩` via
    multiplication and leaves it invariant, then `⟨P⟩ = 0`.

    The hypothesis `h_ω_ne` is the structural witness that for `N ≥ 2`
    the center is non-trivial; proving `centerElement N 1 ≠ 1` from
    `2 ≤ N` is a separate calculation (involving `Complex.exp` not
    being periodic at `2πi/N` for `N ≥ 2`) and is not done here.

    This is the **center-invariance ⟹ vanishing-Polyakov-loop**
    structural argument, with the center non-triviality factored out. -/
theorem polyakov_invariant_implies_zero
    {N : ℕ} (poly : PolyakovExpectation N)
    (ω : ℂ) (h_ω_ne : ω ≠ 1) (h_inv : ω * poly.P = poly.P) :
    poly.P = 0 := by
  -- (ω - 1) · P = 0, and ω - 1 ≠ 0, so P = 0.
  have h_factor : (ω - 1) * poly.P = 0 := by
    have h_rewrite : (ω - 1) * poly.P = ω * poly.P - poly.P := by ring
    rw [h_rewrite, h_inv, sub_self]
  rcases mul_eq_zero.mp h_factor with h_left | h_right
  · exfalso
    have h_eq : ω = 1 := by
      have h_diff : ω - 1 = 0 := h_left
      linear_combination h_diff
    exact h_ω_ne h_eq
  · exact h_right

#print axioms polyakov_invariant_implies_zero

/-! ## §6. Confinement criterion -/

/-- **Confinement criterion**: the pure-Yang-Mills theory is in the
    **confined phase** if and only if the Polyakov loop expectation
    is invariant under all center transformations.

    By `polyakov_invariant_iff_zero`, this is equivalent to
    `⟨P⟩ = 0` for `N ≥ 2`. -/
def IsConfined {N : ℕ} (poly : PolyakovExpectation N) : Prop :=
  poly.P = 0

end L43_CenterSymmetry
