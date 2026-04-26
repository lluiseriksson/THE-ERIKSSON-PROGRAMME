/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lluis Eriksson, Cowork agent (Claude)
-/
import YangMills.L44_LargeNLimit.HooftCoupling

/-!
# `L44_LargeNLimit.PlanarDominance`: Planar dominance and 1/N expansion

This module formalises the **planar-diagram dominance** of pure
Yang-Mills in the **'t Hooft large-N limit**:

  *In the limit `N_c → ∞` with the 't Hooft coupling `λ = g² · N_c`
  held fixed, only **planar (genus-0) Feynman diagrams** contribute
  at leading order; non-planar (genus-`g ≥ 1`) diagrams are suppressed
  by `(1/N²)^g`.*

This is the foundational organising principle of the 1/N expansion.

## Mathematical content

A Feynman diagram in pure Yang-Mills (with double-line / 't Hooft
notation) is a closed orientable 2-surface; its genus `g` is a
topological invariant. The 't Hooft expansion organises diagrams by
genus:

  `D_total = D_planar + (1/N²) · D_genus_1 + (1/N⁴) · D_genus_2 + ...`,

where `D_genus_g` is the contribution from all genus-`g` diagrams.

For **planar diagrams** (genus 0), the contribution is `O(N²)` (from
two index loops). For genus-`g` diagrams, the contribution is
`O(N^(2-2g))`. Hence the **suppression factor** is `N^(2-2g) / N² =
N^(-2g) = (1/N²)^g`.

## Strategy

We encode the genus-suppression factor as a `def` and the planar
dominance principle as a structural statement. The substantive
content of "diagrams" requires Feynman-graph infrastructure not yet
in Mathlib.

## Status

This file is structural physics scaffolding. The substantive
treatment of diagrammatic genus-suppression requires graph-theoretic
+ surface-theoretic infrastructure beyond elementary Mathlib.

**Status (2026-04-25)**: produced in workspace, not yet built with
`lake build`. Statements are short and conceptual.
-/

namespace L44_LargeNLimit

/-! ## §1. The genus-suppression factor -/

/-- **Genus-suppression factor**: at genus `g`, a Feynman diagram in
    pure Yang-Mills is suppressed by `(1/N²)^g` compared to the
    planar (genus-0) diagrams.

    Specifically, for a diagram of genus `g` in the 't Hooft expansion:

      `D_genus(N) = (1/N²)^g · D̃_g`,

    where `D̃_g` is `N`-independent. -/
noncomputable def genusSuppressionFactor (g : ℕ) (N_c : ℕ) : ℝ :=
  ((N_c : ℝ)^2)⁻¹ ^ g

/-- **Genus-0 (planar) is unsuppressed**: `genusSuppressionFactor 0 N = 1`. -/
theorem genusSuppression_zero (N_c : ℕ) :
    genusSuppressionFactor 0 N_c = 1 := by
  unfold genusSuppressionFactor
  rfl

/-- **Genus-1 (torus) suppression**: `genusSuppressionFactor 1 N = 1/N²`. -/
theorem genusSuppression_one {N_c : ℕ} (hN : 1 ≤ N_c) :
    genusSuppressionFactor 1 N_c = 1 / (N_c : ℝ)^2 := by
  unfold genusSuppressionFactor
  rw [pow_one, ← one_div]

#print axioms genusSuppression_one

/-! ## §2. Genus-suppression decreases with `g` -/

/-- **Genus suppression decreases with `g`**: for `N_c ≥ 2`, higher
    genus contributions are smaller in magnitude.

    Specifically: `genusSuppression(g+1) < genusSuppression(g)` for
    `N_c ≥ 2`. -/
theorem genusSuppression_strictAnti {N_c : ℕ} (hN : 2 ≤ N_c) (g : ℕ) :
    genusSuppressionFactor (g + 1) N_c < genusSuppressionFactor g N_c := by
  unfold genusSuppressionFactor
  -- (1/N²)^(g+1) = (1/N²) · (1/N²)^g < (1/N²)^g for 1/N² < 1.
  rw [pow_succ]
  have h_N_pos : (0 : ℝ) < (N_c : ℝ) := by
    have : 0 < N_c := by linarith
    exact_mod_cast this
  have h_N_sq_pos : (0 : ℝ) < (N_c : ℝ)^2 := by positivity
  have h_inv_pos : (0 : ℝ) < ((N_c : ℝ)^2)⁻¹ := inv_pos.mpr h_N_sq_pos
  have h_pow_pos : (0 : ℝ) < ((N_c : ℝ)^2)⁻¹ ^ g := pow_pos h_inv_pos g
  -- Need (1/N²) < 1, i.e., N² > 1. From N_c ≥ 2, N² ≥ 4 > 1.
  have h_N_sq_gt_one : (1 : ℝ) < (N_c : ℝ)^2 := by
    have h_N_ge_two : (2 : ℝ) ≤ (N_c : ℝ) := by exact_mod_cast hN
    nlinarith
  have h_inv_lt_one : ((N_c : ℝ)^2)⁻¹ < 1 := by
    rw [inv_lt_one_iff_of_pos h_N_sq_pos]
    exact h_N_sq_gt_one
  -- So (1/N²)^g · (1/N²) < (1/N²)^g · 1.
  calc ((N_c : ℝ)^2)⁻¹ ^ g * ((N_c : ℝ)^2)⁻¹
      < ((N_c : ℝ)^2)⁻¹ ^ g * 1 :=
          (mul_lt_mul_left h_pow_pos).mpr h_inv_lt_one
    _ = ((N_c : ℝ)^2)⁻¹ ^ g := by ring

#print axioms genusSuppression_strictAnti

/-! ## §3. Planar dominance theorem (structural) -/

/-- **Planar dominance** (structural statement): for any genus
    `g ≥ 1` and `N_c ≥ 2`,

      `genusSuppressionFactor g N_c < 1`,

    i.e., non-planar contributions are strictly smaller than
    planar contributions in magnitude.

    This is the **N → ∞ leading-order content**: only planar diagrams
    survive. -/
theorem planarDominance {N_c : ℕ} (hN : 2 ≤ N_c) {g : ℕ} (hg : 1 ≤ g) :
    genusSuppressionFactor g N_c < 1 := by
  -- By strict-anti monotonicity from g = 0 (which gives 1) to higher g.
  induction g with
  | zero => omega
  | succ k ih =>
    rcases Nat.eq_or_gt_of_le hg with h_eq | h_gt
    · -- g = 1 case: directly from genusSuppression_one.
      have : k = 0 := by omega
      subst this
      rw [genusSuppression_one hN]
      have h_N_pos : (0 : ℝ) < (N_c : ℝ) := by
        have : 0 < N_c := by linarith
        exact_mod_cast this
      have h_N_sq_pos : (0 : ℝ) < (N_c : ℝ)^2 := by positivity
      have h_N_sq_gt_one : (1 : ℝ) < (N_c : ℝ)^2 := by
        have h_N_ge_two : (2 : ℝ) ≤ (N_c : ℝ) := by exact_mod_cast hN
        nlinarith
      rw [div_lt_one h_N_sq_pos]
      exact h_N_sq_gt_one
    · -- g ≥ 2 case: use induction + strict-anti.
      have h_k_ge_one : 1 ≤ k := by omega
      have h_ih := ih h_k_ge_one
      have h_step := genusSuppression_strictAnti hN k
      linarith

#print axioms planarDominance

/-! ## §4. Universal upper bound (substitute for the asymptotic) -/

/-- **Universal upper bound**: for any genus `g ≥ 1` and `N_c ≥ 2`,
    the genus-suppression factor satisfies

      `genusSuppressionFactor g N_c ≤ 1/4`,

    with equality at `g = 1, N_c = 2`.

    The full asymptotic statement (`→ 0` as `N_c → ∞`) requires
    `Filter.Tendsto` machinery; we provide a clean uniform bound
    here, sufficient for "non-planar diagrams are sub-leading by a
    bounded factor". -/
theorem genusSuppression_le_quarter {N_c : ℕ} (hN : 2 ≤ N_c)
    {g : ℕ} (hg : 1 ≤ g) :
    genusSuppressionFactor g N_c ≤ 1/4 := by
  -- For g = 1, N_c = 2: factor = 1/4.
  -- For g ≥ 2 or N_c ≥ 3, factor < 1/4.
  -- We bound by genusSuppressionFactor 1 N_c (use anti monotonicity in g),
  -- then bound that by 1/N_c² ≤ 1/4 (use N_c ≥ 2).
  have h_le_g_one : genusSuppressionFactor g N_c ≤ genusSuppressionFactor 1 N_c := by
    -- For g ≥ 1, factor at g ≤ factor at 1 (anti-monotonicity).
    induction g with
    | zero => omega
    | succ k ih =>
      rcases Nat.eq_or_gt_of_le hg with h_eq | h_gt
      · -- g = 1: equal.
        have : k = 0 := by omega
        subst this
        rfl
      · -- g ≥ 2: use strict-anti to step from k to k+1.
        have h_k_ge_one : 1 ≤ k := by omega
        have h_step := genusSuppression_strictAnti hN k
        have h_ih := ih h_k_ge_one
        linarith
  -- Now bound genusSuppressionFactor 1 N_c by 1/4.
  rw [genusSuppression_one hN] at h_le_g_one
  have h_N_ge_two : (2 : ℝ) ≤ (N_c : ℝ) := by exact_mod_cast hN
  have h_N_sq_ge_four : (4 : ℝ) ≤ (N_c : ℝ)^2 := by nlinarith
  have h_N_sq_pos : (0 : ℝ) < (N_c : ℝ)^2 := by positivity
  have h_inv_le_quarter : 1 / (N_c : ℝ)^2 ≤ 1/4 := by
    rw [div_le_div_iff h_N_sq_pos (by norm_num : (0:ℝ) < 4)]
    linarith
  linarith

#print axioms genusSuppression_le_quarter

end L44_LargeNLimit
