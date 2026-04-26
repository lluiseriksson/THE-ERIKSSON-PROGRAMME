/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lluis Eriksson, Cowork agent (Claude)
-/
import YangMills.L44_LargeNLimit.PlanarDominance
import Mathlib.Topology.Algebra.Order.Compact

/-!
# `L44_LargeNLimit.AsymptoticVanishing`: `genusSuppressionFactor → 0` as `N_c → ∞`

This module addresses **P0 open question §1.4** from `OPEN_QUESTIONS.md`:
the L44 sorry-catch from Phase 444 left the asymptotic vanishing of
the genus-suppression factor as a uniform bound `≤ 1/4` rather than
the full asymptotic statement.

## Mathematical content

For any fixed `g ≥ 1`,

  `genusSuppressionFactor g N_c = ((N_c : ℝ)²)⁻¹^g → 0` as `N_c → ∞`.

This is the **substantive content** of large-N planar dominance: the
non-planar contribution at any fixed genus vanishes in the limit
`N_c → ∞`, not merely being uniformly bounded by 1/4.

## Strategy

We use the **squeeze theorem** with the upper bound:

  `0 ≤ genusSuppressionFactor g N_c ≤ ((N_c)²)⁻¹` for `N_c ≥ 1, g ≥ 1`.

The upper bound follows because `((N_c)²)⁻¹ ≤ 1` for `N_c ≥ 1`, so
raising to power `g` decreases (for `g ≥ 1`).

Then `((N_c)²)⁻¹ → 0` from the chain:
- `(N_c : ℝ) → ∞` as `N_c → ∞` (`Filter.tendsto_natCast_atTop_atTop`).
- `(N_c)² → ∞` (Tendsto.atTop_mul_atTop or pow).
- `((N_c)²)⁻¹ → 0` (Tendsto.inv_atTop_zero or equivalent).

## Status

This file extends L44 with substantive asymptotic content. **Status
(2026-04-25 Phase 461)**: produced in workspace, not yet built with
`lake build`. The proof uses `Filter.Tendsto` machinery; specific
lemma names may have drifted in current Mathlib master.

If a sorry-catch reoccurs, the resolution is to hypothesis-condition
on the inner step that overreaches.
-/

namespace L44_LargeNLimit

open Filter Topology

/-! ## §1. The asymptotic vanishing of `genusSuppressionFactor` -/

/-- **`genusSuppressionFactor_tendsto_zero`**: for any fixed `g ≥ 1`,

      `genusSuppressionFactor g N_c → 0` as `N_c → ∞`.

    This closes the L44 sorry-catch from Phase 444 by providing the
    full asymptotic statement (the prior `genusSuppression_le_quarter`
    gave only a uniform bound). -/
theorem genusSuppressionFactor_tendsto_zero {g : ℕ} (hg : 1 ≤ g) :
    Tendsto (fun N_c : ℕ => genusSuppressionFactor g N_c) atTop (𝓝 0) := by
  -- Squeeze: 0 ≤ genusSuppressionFactor g N_c ≤ ((N_c)²)⁻¹ for N_c ≥ 1.
  -- Lower bound: ≥ 0 always.
  -- Upper bound: ((N_c)²)⁻¹ ≤ 1 ⟹ ((N_c)²)⁻¹^g ≤ ((N_c)²)⁻¹ for g ≥ 1.
  have h_inv_sq_to_zero : Tendsto (fun N_c : ℕ => ((N_c : ℝ)^2)⁻¹) atTop (𝓝 0) := by
    -- (N_c : ℝ)^2 → ∞, so inverse → 0.
    have h_lin : Tendsto (fun N_c : ℕ => (N_c : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop
    have h_sq : Tendsto (fun N_c : ℕ => (N_c : ℝ)^2) atTop atTop := by
      -- (N_c)² = (N_c) · (N_c).
      have : Tendsto (fun N_c : ℕ => (N_c : ℝ) * (N_c : ℝ)) atTop atTop :=
        h_lin.atTop_mul_atTop h_lin
      convert this using 1
      ext N_c
      ring
    -- inverse of atTop tends to 0.
    exact h_sq.inv_tendsto_atTop
  -- Squeeze with constant 0 below and (1/N²) above.
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h_inv_sq_to_zero
  · -- For sufficiently large N_c (N_c ≥ 1 suffices), 0 ≤ genusSuppressionFactor g N_c.
    filter_upwards [eventually_ge_atTop 1] with N_c hN_c
    unfold genusSuppressionFactor
    have h_N_pos : (0 : ℝ) < (N_c : ℝ) := by exact_mod_cast hN_c
    have h_N_sq_pos : (0 : ℝ) < (N_c : ℝ)^2 := by positivity
    positivity
  · -- For N_c ≥ 1, genusSuppressionFactor g N_c ≤ ((N_c)²)⁻¹.
    filter_upwards [eventually_ge_atTop 1] with N_c hN_c
    unfold genusSuppressionFactor
    -- ((N_c)²)⁻¹^g ≤ ((N_c)²)⁻¹ since ((N_c)²)⁻¹ ∈ [0, 1] and g ≥ 1.
    have h_N_pos : (0 : ℝ) < (N_c : ℝ) := by exact_mod_cast hN_c
    have h_N_sq_pos : (0 : ℝ) < (N_c : ℝ)^2 := by positivity
    have h_inv_pos : (0 : ℝ) < ((N_c : ℝ)^2)⁻¹ := inv_pos.mpr h_N_sq_pos
    have h_N_sq_ge_one : (1 : ℝ) ≤ (N_c : ℝ)^2 := by
      have h_N_ge_one : (1 : ℝ) ≤ (N_c : ℝ) := by exact_mod_cast hN_c
      nlinarith
    have h_inv_le_one : ((N_c : ℝ)^2)⁻¹ ≤ 1 := by
      rw [inv_le_one_iff_one_le_of_pos h_N_sq_pos]
      exact h_N_sq_ge_one
    -- For 0 ≤ a ≤ 1 and g ≥ 1: a^g ≤ a.
    -- Equivalently a^g = a · a^(g-1) ≤ a · 1 = a since a^(g-1) ≤ 1.
    rcases hg.lt_or_eq with h_g_gt | h_g_eq
    · -- g ≥ 2 case: use a^g = a · a^(g-1) and a^(g-1) ≤ 1.
      have h_g_pred : g = (g - 1) + 1 := by omega
      rw [h_g_pred, pow_succ]
      have h_pred_pow_le_one : ((N_c : ℝ)^2)⁻¹^(g - 1) ≤ 1 := by
        apply pow_le_one (le_of_lt h_inv_pos) h_inv_le_one
      have h_inv_nn : (0 : ℝ) ≤ ((N_c : ℝ)^2)⁻¹ := le_of_lt h_inv_pos
      calc ((N_c : ℝ)^2)⁻¹ ^ (g - 1) * ((N_c : ℝ)^2)⁻¹
          ≤ 1 * ((N_c : ℝ)^2)⁻¹ :=
            mul_le_mul_of_nonneg_right h_pred_pow_le_one h_inv_nn
        _ = ((N_c : ℝ)^2)⁻¹ := one_mul _
    · -- g = 1 case: trivial.
      rw [← h_g_eq, pow_one]

#print axioms genusSuppressionFactor_tendsto_zero

end L44_LargeNLimit
