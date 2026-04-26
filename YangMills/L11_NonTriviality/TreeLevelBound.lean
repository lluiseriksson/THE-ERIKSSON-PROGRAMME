/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cowork agent (Claude), under supervision of Lluis Eriksson
-/
import Mathlib
import YangMills.L11_NonTriviality.PlaquetteFourPointFunction

/-!
# Tree-level lower bound on the 4-point function (Bloque-4 §8.5)

This module formalises the **tree-level lower bound**:

  T_tree = (C_4(N) / N^4) · ḡ^4 · Γ(x_1, ..., x_4)

where:
* `C_4(N) > 0` is the **fourth moment** of the Haar measure on
  `SU(N)` (strictly positive for non-abelian groups).
* `Γ > 0` is a product of terminal-scale propagators evaluated at
  separated points; bounded below by `e^{-4cR}` for points at
  separation `R`.

This gives `T_tree ≥ (C_4(N)/N^4) · ḡ^4 · e^{-4cR}`, which is
strictly positive.

## Strategic placement

This is **Phase 114** of the L11_NonTriviality block.

## Oracle target

`[propext, Classical.choice, Quot.sound]`.

-/

namespace YangMills.L11_NonTriviality

open MeasureTheory

/-! ## §1. Group-theoretic constant C_4(N) -/

/-- The **fourth moment of Haar on SU(N)** for the trace observable.
    For non-abelian SU(N), N ≥ 2: `C_4(N) > 0`.

    Concretely: `C_4(N) = ∫_{SU(N)} (Re Tr U)^4 d_Haar - 3 (∫ (Re Tr U)^2)^2`.

    By symmetry + group invariance, this is a **strictly positive
    constant** depending only on N. -/
structure HaarFourthMomentConstant (N_c : ℕ) where
  /-- The constant value. -/
  C_4 : ℝ
  /-- Strictly positive for non-abelian SU(N). -/
  C_4_pos : 2 ≤ N_c → 0 < C_4

/-! ## §2. Terminal-scale propagator product -/

/-- The **terminal-scale propagator product** `Γ(x_1, ..., x_4)`,
    bounded below by `e^{-4cR}` for points pairwise separated by R. -/
structure TerminalPropagatorProduct where
  /-- The decay rate. -/
  c : ℝ
  c_pos : 0 < c
  /-- The product value at given points and distance. -/
  Γ : (Fin 4 → ℝ) → (Fin 4 → ℝ) → (Fin 4 → ℝ) → (Fin 4 → ℝ) → ℝ
  /-- Lower bound: Γ ≥ e^{-4cR} for points at mutual distance ≥ R. -/
  bound : ∀ (x_1 x_2 x_3 x_4 : Fin 4 → ℝ) (R : ℝ),
    MutualDistanceBound x_1 x_2 x_3 x_4 R →
    Real.exp (-4 * c * R) ≤ Γ x_1 x_2 x_3 x_4

/-! ## §3. The tree-level bound theorem -/

/-- The **tree-level contribution** at terminal scale:

  T_tree = (C_4(N)/N^4) · ḡ^4 · Γ(x_1, ..., x_4).

For N_c ≥ 2 and 0 < ḡ, this is strictly positive. -/
noncomputable def treeLevelContribution
    {N_c : ℕ} (M : HaarFourthMomentConstant N_c)
    (P : TerminalPropagatorProduct)
    (ḡ : ℝ)
    (x_1 x_2 x_3 x_4 : Fin 4 → ℝ) : ℝ :=
  (M.C_4 / (N_c : ℝ) ^ 4) * ḡ ^ 4 * P.Γ x_1 x_2 x_3 x_4

/-- **Tree-level lower bound (Bloque-4 §8.5 lower bound at terminal scale)**:
    for N_c ≥ 2, 0 < ḡ ≤ 1, and points at mutual distance ≥ R:

      |T_tree| ≥ (C_4(N)/N^4) · ḡ^4 · e^{-4cR} =: c_0 · ḡ^4

    where `c_0 = (C_4(N)/N^4) · e^{-4cR}` depends on R and the
    group-theoretic constants. -/
theorem treeLevel_lowerBound
    {N_c : ℕ} (hN_c : 2 ≤ N_c)
    (M : HaarFourthMomentConstant N_c)
    (P : TerminalPropagatorProduct)
    (ḡ : ℝ) (hḡ : 0 < ḡ)
    (x_1 x_2 x_3 x_4 : Fin 4 → ℝ) (R : ℝ)
    (hR : MutualDistanceBound x_1 x_2 x_3 x_4 R) :
    (M.C_4 / (N_c : ℝ) ^ 4) * ḡ ^ 4 * Real.exp (-4 * P.c * R) ≤
    treeLevelContribution M P ḡ x_1 x_2 x_3 x_4 := by
  unfold treeLevelContribution
  have hC4_pos := M.C_4_pos hN_c
  have hN_pos : (0 : ℝ) < (N_c : ℝ) ^ 4 := by
    have : (0 : ℝ) < (N_c : ℝ) := by
      exact_mod_cast Nat.lt_of_lt_of_le (by norm_num : 0 < 2) hN_c
    positivity
  have hC4_div_pos : (0 : ℝ) < M.C_4 / (N_c : ℝ) ^ 4 := div_pos hC4_pos hN_pos
  have hḡ4_pos : (0 : ℝ) < ḡ ^ 4 := by positivity
  have h_Γ_lb := P.bound x_1 x_2 x_3 x_4 R hR
  -- The conclusion is monotone in Γ.
  apply mul_le_mul_of_nonneg_left h_Γ_lb
  exact mul_nonneg hC4_div_pos.le hḡ4_pos.le

#print axioms treeLevel_lowerBound

/-! ## §4. Coordination note -/

/-
This file is **Phase 114** of the L11_NonTriviality block.

## Status

* `HaarFourthMomentConstant`, `TerminalPropagatorProduct` data structures.
* `treeLevelContribution` definition.
* `treeLevel_lowerBound` theorem with **full proof, NO sorries**.

## What's done

The tree-level lower bound is **fully proved at the abstract level**:
given the group-theoretic constant `C_4(N) > 0`, the propagator
product lower bound, and `ḡ > 0`, the tree-level term is bounded
below by `(C_4/N^4) · ḡ^4 · e^{-4cR}`.

## What's NOT done

* Concrete value of `C_4(N)` for SU(N), N ≥ 2 (would require Mathlib's
  Haar integration on SU(N) infrastructure).
* The propagator product bound from Bloque-4 Lemma B.1.

## Strategic value

Phase 114 provides the **non-vanishing tree-level term** which is
the substantive ingredient of Bloque-4 Theorem 8.7's non-triviality
argument.

Cross-references:
- Phase 113: `PlaquetteFourPointFunction.lean`.
- Phase 115: `PolymerRemainderBound.lean` (next).
- Bloque-4 §8.5 lower-bound paragraph.
-/

end YangMills.L11_NonTriviality
