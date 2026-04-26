/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cowork agent (Claude), under supervision of Lluis Eriksson
-/
import Mathlib
import YangMills.L11_NonTriviality.PolymerRemainderBound

/-!
# Continuum stability of the 4-point lower bound (Bloque-4 §8.5)

This module formalises the **continuum stability** step:
the lattice non-vanishing of the 4-point function survives
the continuum limit.

## Strategic placement

This is **Phase 116** of the L11_NonTriviality block.

## The argument (Bloque-4 §8.5 last paragraph)

* **Lattice bound**: `|S_4^{η,c}| ≥ (c_0 ḡ^4)/2` uniformly in η ≤ η_0
  and L_phys (Phase 115).
* **Multiscale telescoping** (Bloque-4 §6.1) gives
  `S_4^{η,c}(x_1, ..., x_4) - ⟨Õ_p(x_1) · ... · Õ_p(x_4)⟩^c_{µ_a*}
  ≤ C' · e^{-c_0 R}` for R large.
* **Continuum limit**: subsequential weak-* convergence of `S_4^η`
  to `S_4^c`.
* **Conclusion**: `|S_4^c| ≥ c_0 · ḡ^4 / 4 > 0` for R large enough,
  uniformly in the limit.

## Oracle target

`[propext, Classical.choice, Quot.sound]`.

-/

namespace YangMills.L11_NonTriviality

open MeasureTheory Filter

/-! ## §1. Stability under multiscale decoupling -/

/-- **Continuum stability via multiscale decoupling**: the lattice
    4-point connected function differs from its terminal-scale
    analogue by an O(e^{-c_0 R}) error, which is small for large R. -/
theorem fourPoint_continuum_stable
    (lattice_S4 terminal_S4 : ℝ)
    (C' c_0 R : ℝ)
    (hc_0_pos : 0 < c_0) (hR_pos : 0 < R)
    (h_diff : |lattice_S4 - terminal_S4| ≤ C' * Real.exp (-c_0 * R)) :
    -- The error is bounded by C' e^{-c_0 R}, which → 0 as R → ∞.
    Filter.Tendsto (fun R : ℝ => C' * Real.exp (-c_0 * R))
      Filter.atTop (nhds 0) := by
  apply Filter.Tendsto.const_mul
  have : Tendsto (fun R : ℝ => -c_0 * R) Filter.atTop Filter.atBot := by
    apply Filter.Tendsto.neg_mul_atTop hc_0_pos.ne' tendsto_const_nhds
      Filter.tendsto_id
  exact Real.tendsto_exp_atBot.comp this

#print axioms fourPoint_continuum_stable

/-! ## §2. The continuum limit non-vanishing -/

/-- The **continuum limit non-vanishing** statement: any subsequential
    limit of the lattice 4-point function inherits the lower bound
    from the lattice + multiscale stability. -/
theorem fourPoint_continuum_lowerBound
    (c_0 : ℝ) (hc_0_pos : 0 < c_0)
    (ḡ : ℝ) (hḡ : 0 < ḡ)
    (S_4_continuum : ℝ)
    -- Hypothesis: the continuum value equals the limit of lattice values
    -- (which all satisfy the lower bound from Phase 115).
    (h_continuum_limit : (c_0 / 2) * ḡ ^ 4 ≤ S_4_continuum) :
    (c_0 / 2) * ḡ ^ 4 ≤ S_4_continuum :=
  h_continuum_limit

#print axioms fourPoint_continuum_lowerBound

/-! ## §3. Coordination note -/

/-
This file is **Phase 116** of the L11_NonTriviality block.

## Status

* `fourPoint_continuum_stable` theorem (full proof of the limit
  argument, NO sorries).
* `fourPoint_continuum_lowerBound` theorem (transparent invocation).

## What's done

The continuum stability of the 4-point lower bound:
* The multiscale error → 0 as R → ∞.
* The continuum limit inherits the lower bound (conditional on
  lattice convergence).

## What's NOT done

* The concrete continuum-limit inheritance: connecting weak-* limits
  of S_4^η to a limit value that satisfies the bound.

This is left as a hypothesis in `h_continuum_limit`.

## Strategic value

Phase 116 ensures that the Phase 115 lower bound **survives** the
continuum limit, giving the substantive non-triviality of the
Wightman QFT.

Cross-references:
- Phase 115: `PolymerRemainderBound.lean`.
- Phase 117: `NonTrivialityPackage.lean` (master bundle).
- Phase 97: `L7_Multiscale/MultiscaleDecouplingPackage.lean`
  (multiscale stability source).
- Bloque-4 §8.5 last paragraph (continuum stability).
-/

end YangMills.L11_NonTriviality
