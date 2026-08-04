/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson

O-3b(iii): where the physics enters — a convolution kernel whose character
coefficients are non-negative, and the Z_2 Wilson weight as a concrete
instance.

Charter: docs/O-BRIDGE-CHARTER.md, AMENDMENT 6.
-/

import Mathlib
import YangMills.OS.PSDKernel

/-!
# O-3b(iii) — the Wilson weight as a non-negative character combination

## The gap this closes

O-3b(i) proves that a crossing kernel which is a non-negative combination
`∑ i, c i · φ i x · conj (φ i y)` is positive semidefinite, and O-3b(ii) proves
that such a kernel makes the Osterwalder--Seiler pairing positive.  Both
modules state explicitly that they do **not** claim any actual Boltzmann factor
has that form.  This module supplies one that does.

## Two steps

`isCharCombo_of_convolution` is the bridge from a *weight* to a *kernel*: for a
family of functions multiplicative in the group difference,
`χ i (x - y) = χ i x · conj (χ i y)`, a weight with non-negative character
coefficients gives a crossing kernel in the class of O-3b(i).  It is stated for
an arbitrary additive group and an arbitrary such family, so no character API
is needed and nothing depends on how `ZMod N` characters happen to be packaged.

`z2Wilson_isCharCombo` is the instance, and it is the genuine Wilson weight, not
a toy.  For `Z_2` the plaquette variable is `s = ±1` and the Wilson factor is
`exp (β s)`, whose expansion in the two characters of `Z_2` is
`c₀ + c₁ χ₁` with

  `c₀ = (e^β + e^{-β})/2`,   `c₁ = (e^β - e^{-β})/2`,

and **both are non-negative exactly when `β ≥ 0`** — the first always, the
second by monotonicity of `exp`.  The coefficients are written in that explicit
form rather than as `cosh`/`sinh` so that the proof needs no hyperbolic-function
lemmas at all.

## Scope

This settles the crossing-kernel positivity question for `Z_2` at non-negative
coupling.  It says nothing about `Z_N` for `N > 2` with the Wilson action, where
the coefficients are discrete Bessel-type sums and their non-negativity is a
real analytic fact that is **not** established here.  It says nothing about
`SU(N)`, the continuum limit, or a mass gap.

Oracle target: `[propext, Classical.choice, Quot.sound]`. No sorry, no axioms.
-/

namespace YangMills.OS

set_option linter.unusedSectionVars false

open Finset

/-! ## From a weight to a crossing kernel -/

/-- **The bridge from weights to kernels.**  If the family `χ` is multiplicative
in the group difference and the weight `k` has non-negative coefficients in it,
then the convolution kernel `(x,y) ↦ k (x - y)` is a non-negative character
combination, hence positive semidefinite by O-3b(i).

Stated for an arbitrary additive group and an arbitrary such family: no
character API is used, so nothing here depends on how the characters of a
particular group are packaged in the library. -/
theorem isCharCombo_of_convolution {X : Type*} [AddCommGroup X] [Fintype X]
    [DecidableEq X] {ι : Type*} [Fintype ι] {c : ι → ℝ} {χ : ι → X → ℂ} {k : X → ℂ}
    (hc : ∀ i, 0 ≤ c i)
    (hχ : ∀ i x y, χ i (x - y) = χ i x * (starRingEnd ℂ) (χ i y))
    (hk : ∀ u, k u = ∑ i, (c i : ℂ) * χ i u) :
    IsCharCombo c χ (fun x y => k (x - y)) where
  coeff_nonneg := hc
  eq := by
    intro x y
    rw [hk]
    exact Finset.sum_congr rfl fun i _ => by rw [hχ i x y, mul_assoc]

/-! ## The two characters of `Z_2` -/

/-- The nontrivial character of `Z_2`, as a complex-valued function. -/
noncomputable def z2char : ZMod 2 → ℂ := fun u => if u = 0 then 1 else -1

theorem z2char_zero : z2char 0 = 1 := by simp [z2char]

theorem z2char_one : z2char 1 = -1 := by simp [z2char]

/-- `Z_2` has only two elements. -/
theorem zmod_two_cases (u : ZMod 2) : u = 0 ∨ u = 1 := by
  revert u
  decide

/-- The nontrivial character is multiplicative in the difference — the property
`isCharCombo_of_convolution` consumes. -/
theorem z2char_sub (x y : ZMod 2) :
    z2char (x - y) = z2char x * (starRingEnd ℂ) (z2char y) := by
  rcases zmod_two_cases x with hx | hx <;> rcases zmod_two_cases y with hy | hy <;>
    subst hx <;> subst hy <;>
    · norm_num [z2char, show ((0 : ZMod 2) - 0) = 0 by decide,
        show ((0 : ZMod 2) - 1) = 1 by decide,
        show ((1 : ZMod 2) - 0) = 1 by decide,
        show ((1 : ZMod 2) - 1) = 0 by decide]

/-! ## The `Z_2` Wilson weight -/

/-- The `Z_2` Wilson single-plaquette factor: `exp (β s)` with `s = ±1`, written
on `ZMod 2` with `0 ↦ s = +1`. -/
noncomputable def z2Wilson (β : ℝ) : ZMod 2 → ℝ :=
  fun u => if u = 0 then Real.exp β else Real.exp (-β)

theorem z2Wilson_pos (β : ℝ) (u : ZMod 2) : 0 < z2Wilson β u := by
  unfold z2Wilson
  split <;> exact Real.exp_pos _

/-- The two character coefficients of the `Z_2` Wilson weight, written
explicitly so that no hyperbolic-function lemma is needed. -/
noncomputable def z2Coeff (β : ℝ) : Fin 2 → ℝ :=
  fun i => if i = 0 then (Real.exp β + Real.exp (-β)) / 2
           else (Real.exp β - Real.exp (-β)) / 2

/-- The characters indexed to match. -/
noncomputable def z2Chars : Fin 2 → ZMod 2 → ℂ :=
  fun i => if i = 0 then (fun _ => 1) else z2char

/-- **Both coefficients are non-negative exactly when the coupling is.**  The
first always; the second by monotonicity of `exp`. -/
theorem z2Coeff_nonneg {β : ℝ} (hβ : 0 ≤ β) (i : Fin 2) : 0 ≤ z2Coeff β i := by
  unfold z2Coeff
  split
  · positivity
  · have : Real.exp (-β) ≤ Real.exp β := Real.exp_le_exp.mpr (by linarith)
    linarith

/-- The character expansion of the `Z_2` Wilson weight. -/
theorem z2Wilson_expansion (β : ℝ) (u : ZMod 2) :
    ((z2Wilson β u : ℝ) : ℂ) = ∑ i : Fin 2, (z2Coeff β i : ℂ) * z2Chars i u := by
  rcases zmod_two_cases u with hu | hu <;> subst hu <;>
    · simp [z2Wilson, z2Coeff, z2Chars, z2char, Fin.sum_univ_two]
      push_cast
      ring

/-- The characters used are multiplicative in the difference. -/
theorem z2Chars_sub (i : Fin 2) (x y : ZMod 2) :
    z2Chars i (x - y) = z2Chars i x * (starRingEnd ℂ) (z2Chars i y) := by
  unfold z2Chars
  split
  · simp
  · exact z2char_sub x y

/-- **The instance.**  At non-negative coupling the `Z_2` Wilson crossing kernel
is a non-negative character combination, hence positive semidefinite.  This is
the actual Wilson weight; the physics content of O-3b enters exactly here. -/
theorem z2Wilson_isCharCombo {β : ℝ} (hβ : 0 ≤ β) :
    IsCharCombo (z2Coeff β) z2Chars
      (fun x y => ((z2Wilson β (x - y) : ℝ) : ℂ)) :=
  isCharCombo_of_convolution (z2Coeff_nonneg hβ) z2Chars_sub
    (fun u => z2Wilson_expansion β u)

/-- Consequently the `Z_2` Wilson crossing kernel is PSD at `β ≥ 0`. -/
theorem z2Wilson_isPSDKernel {β : ℝ} (hβ : 0 ≤ β) :
    IsPSDKernel (fun x y => ((z2Wilson β (x - y) : ℝ) : ℂ)) :=
  isPSDKernel_of_charCombo (z2Wilson_isCharCombo hβ)

/-- Non-vacuity of the coupling range: at `β > 0` the second coefficient is
strictly positive, so the weight is genuinely not constant and the instance is
not the degenerate `β = 0` one. -/
theorem z2Coeff_one_pos {β : ℝ} (hβ : 0 < β) : 0 < z2Coeff β 1 := by
  unfold z2Coeff
  simp only [if_neg (by decide : ¬((1 : Fin 2) = 0))]
  have : Real.exp (-β) < Real.exp β := Real.exp_lt_exp.mpr (by linarith)
  linarith

end YangMills.OS
