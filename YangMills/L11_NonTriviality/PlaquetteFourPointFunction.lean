/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cowork agent (Claude), under supervision of Lluis Eriksson
-/
import Mathlib

/-!
# Plaquette four-point function (Bloque-4 §8.5 setup)

This module formalises the **plaquette four-point function** that is
the central object of Bloque-4 Theorem 8.7 (non-triviality of the
Wightman theory).

## Strategic placement

This is **Phase 113** of the L11_NonTriviality block (Phases 113-117).

## Definition (Bloque-4 §8.5)

For four lattice points `x_1, x_2, x_3, x_4 ∈ Λ_η` with mutual
distances `≫ a_*`, the **connected four-point Schwinger function**:

  S_4^{η,c}(x_1, ..., x_4) := ⟨O_p(x_1) · O_p(x_2) · O_p(x_3) · O_p(x_4)⟩^c

where `O_p = N^{-1} · Re Tr U(∂p)` is the **plaquette observable**
(real part of the trace of the gauge field around plaquette `p`).

Bloque-4 Theorem 8.7 establishes:

  |S_4^{η,c}(x_1, x_2, x_3, x_4)| ≥ c_0 · ḡ^4 > 0

uniformly in `η ≤ η_0` and `L_phys`, for explicit constants `c_0 > 0`
and the terminal coupling `ḡ`.

This **non-vanishing** property excludes the trivial (Gaussian)
theory and certifies that the reconstructed Wightman QFT is
genuinely interacting.

## Oracle target

`[propext, Classical.choice, Quot.sound]`.
-/

namespace YangMills.L11_NonTriviality

open MeasureTheory

/-! ## §1. Plaquette observable -/

/-- A **plaquette observable datum**: an evaluation function
    representing `O_p = N^{-1} · Re Tr U(∂p)` on a lattice gauge
    configuration. -/
structure PlaquetteObservable
    (X : Type*) [MeasurableSpace X] where
  /-- The evaluation: at each lattice point and configuration. -/
  eval : (Fin 4 → ℝ) → X → ℝ
  /-- Boundedness: |O_p(x)(U)| ≤ 1 for all gauge configurations. -/
  bound : ∀ (x : Fin 4 → ℝ) (U : X), |eval x U| ≤ 1

/-! ## §2. Connected four-point function -/

/-- The **connected four-point Schwinger function** of a plaquette
    observable.

    Defined as the connected correlator of `O_p` evaluated at four
    lattice points. -/
noncomputable def connectedFourPointFunction
    {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (O : PlaquetteObservable X)
    (x_1 x_2 x_3 x_4 : Fin 4 → ℝ) : ℝ :=
  -- The connected 4-point function via cumulant expansion:
  -- ⟨O₁ O₂ O₃ O₄⟩ - ⟨O₁ O₂⟩⟨O₃ O₄⟩ - ⟨O₁ O₃⟩⟨O₂ O₄⟩ - ⟨O₁ O₄⟩⟨O₂ O₃⟩
  --   + 2·⟨O₁⟩⟨O₂⟩⟨O₃⟩⟨O₄⟩
  ∫ U, O.eval x_1 U * O.eval x_2 U * O.eval x_3 U * O.eval x_4 U ∂μ -
  (∫ U, O.eval x_1 U * O.eval x_2 U ∂μ) *
    (∫ U, O.eval x_3 U * O.eval x_4 U ∂μ) -
  (∫ U, O.eval x_1 U * O.eval x_3 U ∂μ) *
    (∫ U, O.eval x_2 U * O.eval x_4 U ∂μ) -
  (∫ U, O.eval x_1 U * O.eval x_4 U ∂μ) *
    (∫ U, O.eval x_2 U * O.eval x_3 U ∂μ) +
  2 * (∫ U, O.eval x_1 U ∂μ) * (∫ U, O.eval x_2 U ∂μ) *
      (∫ U, O.eval x_3 U ∂μ) * (∫ U, O.eval x_4 U ∂μ)

/-! ## §3. Mutual-distance hypothesis -/

/-- A **mutual-distance hypothesis**: the four lattice points are
    pairwise separated by at least distance `R`. -/
def MutualDistanceBound (x_1 x_2 x_3 x_4 : Fin 4 → ℝ) (R : ℝ) : Prop :=
  ∀ (i j : Fin 4),
    -- Pick the appropriate pair (x_i, x_j)
    -- For simplicity here we abstract via a placeholder distance.
    -- Concrete formulation: ‖x_i - x_j‖ ≥ R for i ≠ j.
    True

/-! ## §4. Coordination note -/

/-
This file is **Phase 113** of the L11_NonTriviality block.

## Status

* `PlaquetteObservable` data structure.
* `connectedFourPointFunction` definition (full cumulant expansion).
* `MutualDistanceBound` predicate (placeholder).

## What's done

The structural setup of Bloque-4 §8.5: plaquette observable,
connected 4-point function, distance hypothesis.

## What's NOT done

* Concrete plaquette observable construction from `Matrix.specialUnitaryGroup`.
* `MutualDistanceBound` predicate body (currently `True`).

## Strategic value

Phase 113 provides the **basic objects** for Phases 114-117 (tree-level
bound, polymer correction, continuum stability, master bundle).

Cross-references:
- Bloque-4 §8.5 (Non-Triviality).
- Phase 114: `TreeLevelBound.lean`.
-/

end YangMills.L11_NonTriviality
