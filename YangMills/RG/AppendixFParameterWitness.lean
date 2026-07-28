/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import Mathlib
import YangMills.RG.AppendixFSecondUrsellLeafSummation
import YangMills.RG.PolymerClusterWithHolesBridge

/-!
# Numeric parameter witness for the Appendix-F conditional chain
(`hRpoly` campaign — P3.5 brick B1)

`docs/HRPOLY-CAMPAIGN-PLAN.md` §3bis, item (O2).  The composed H# residual
chain (raw bound → K# → weighted tree → H# → `SingleScaleUVDecay`) carries a
family of scalar side conditions: the geometric smallness
`(3^d)² · e^{−κ₀} · 2^{3^d+1} < 1`, the rate margin `κ ≥ 4κ₀ + 3`, the
amplitude window `0 ≤ H₀ ≤ 1`, and the second-Ursell leaf/root half-budget
`leafConstant · (2·H₀·rootSumConstant) ≤ 1/2`.  Until this module, NO
instantiation anywhere in the repository showed those conditions to be
jointly satisfiable — a house-rule-3 exposure (a conditional chain whose
parameter region might be empty is one vacuous-weakening away from a hollow
claim).

**The witness.**  `κ₀(d) := (3^d + 1)·log 2 + 2d·log 3 + 1` makes the
geometric smallness EXACT: the product collapses to `e⁻¹`
(`appendixFWitnessKappa0_geometric_eq` is an equality, not an estimate).
Consequently `appendixFHoleRootSumConstant d κ₀(d) = (1 − e⁻¹)⁻¹ ≤ 2`,
`appendixFSecondUrsellMomentConstant ≤ 2` (as `κ₀(d) ≥ 1`),
`appendixFSecondUrsellLeafConstant ≤ 16`, and `H₀ := 1/256` satisfies the
half-budget with a factor-2 margin (`16·(2·H₀·2) = 1/4 ≤ 1/2`).  The rate is
`κ := 4κ₀ + 3`, matching the summability-margin hypothesis
`κ ≥ 4κ₀ + 3` of `PolymerClusterWithHolesBridge`.

The θ-shifted budget `polymerClusterResidualRate (4κ₀+3+θ) κ₀ − θ = κ₀`
(consumed by ladder brick B3, where `θ = 1 + 3^d·B` is the B2 compression
constant) is proved as exact arithmetic.

**Honest scope.**  This module proves the parameter REGION of the
conditional chain is non-empty at explicit numbers.  It does not prove the
raw YM activity estimate (O1/hRpoly proper), any Appendix-F source term, the
remaining O4/O5 ladder bricks, mass gap, or Clay.

Oracle target: `[propext, Classical.choice, Quot.sound]`.  No sorry, no axioms.
-/

namespace YangMills.RG

/-- The B1 witness decay rate: `κ₀(d) = (3^d + 1)·log 2 + 2d·log 3 + 1`.
Chosen so the Appendix-F geometric smallness product collapses exactly to
`e⁻¹`. -/
noncomputable def appendixFWitnessKappa0 (d : ℕ) : ℝ :=
  ((3 ^ d + 1 : ℕ) : ℝ) * Real.log 2 + ((2 * d : ℕ) : ℝ) * Real.log 3 + 1

/-- The witness rate is at least `1` (both log terms are nonnegative). -/
theorem one_le_appendixFWitnessKappa0 (d : ℕ) :
    1 ≤ appendixFWitnessKappa0 d := by
  have h2 : (0:ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have h3 : (0:ℝ) ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have hn2 : (0:ℝ) ≤ ((3 ^ d + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hn3 : (0:ℝ) ≤ ((2 * d : ℕ) : ℝ) := Nat.cast_nonneg _
  have := mul_nonneg hn2 h2
  have := mul_nonneg hn3 h3
  unfold appendixFWitnessKappa0
  linarith

/-- The witness rate is positive. -/
theorem appendixFWitnessKappa0_pos (d : ℕ) : 0 < appendixFWitnessKappa0 d :=
  lt_of_lt_of_le one_pos (one_le_appendixFWitnessKappa0 d)

/-- **Exact collapse of the geometric smallness product.**  At the witness
rate the Appendix-F geometric product is EXACTLY `e⁻¹` — the smallness
condition holds by an identity, not an estimate. -/
theorem appendixFWitnessKappa0_geometric_eq (d : ℕ) :
    ((3 ^ d : ℕ) : ℝ) ^ 2 *
      (Real.exp (-(appendixFWitnessKappa0 d)) * 2 ^ (3 ^ d + 1)) =
    Real.exp (-1) := by
  have hexp : Real.exp (appendixFWitnessKappa0 d)
      = 2 ^ (3 ^ d + 1) * 3 ^ (2 * d) * Real.exp 1 := by
    unfold appendixFWitnessKappa0
    rw [Real.exp_add, Real.exp_add, Real.exp_nat_mul, Real.exp_nat_mul,
      Real.exp_log (by norm_num : (0:ℝ) < 2),
      Real.exp_log (by norm_num : (0:ℝ) < 3)]
  have hcast : ((3 ^ d : ℕ) : ℝ) ^ 2 = (3 : ℝ) ^ (2 * d) := by
    push_cast
    rw [← pow_mul, mul_comm d 2]
  have h2ne : ((2:ℝ)) ^ (3 ^ d + 1) ≠ 0 := by positivity
  have h3ne : ((3:ℝ)) ^ (2 * d) ≠ 0 := by positivity
  have hene : Real.exp 1 ≠ 0 := Real.exp_ne_zero 1
  rw [hcast, Real.exp_neg, hexp, Real.exp_neg]
  field_simp [h2ne, h3ne, hene]

/-- The Appendix-F geometric smallness condition holds at the witness rate
(in the exact field shape consumed by the CMP116 source-assumption
structures). -/
theorem appendixFWitnessKappa0_geometric_lt_one (d : ℕ) :
    ((3 ^ d : ℕ) : ℝ) ^ 2 *
      (Real.exp (-(appendixFWitnessKappa0 d)) * 2 ^ (3 ^ d + 1)) < 1 := by
  rw [appendixFWitnessKappa0_geometric_eq]
  rw [← Real.exp_zero]
  exact Real.exp_lt_exp.mpr (by norm_num)

/-- `e⁻¹ ≤ 1/2` (from `2 ≤ e`). -/
private lemma exp_neg_one_le_half : Real.exp (-1) ≤ 1 / 2 := by
  have h2e : (2:ℝ) ≤ Real.exp 1 := by
    have := Real.add_one_le_exp (1:ℝ)
    linarith
  rw [Real.exp_neg]
  rw [inv_eq_one_div]
  rw [div_le_div_iff₀ (Real.exp_pos 1) (by norm_num : (0:ℝ) < 2)]
  linarith

/-- At the witness rate the rooted geometric constant is at most `2`. -/
theorem appendixFHoleRootSumConstant_witness_le_two (d : ℕ) :
    appendixFHoleRootSumConstant d (appendixFWitnessKappa0 d) ≤ 2 := by
  unfold appendixFHoleRootSumConstant
  have heq := appendixFWitnessKappa0_geometric_eq d
  rw [heq]
  have hle : Real.exp (-1) ≤ 1 / 2 := exp_neg_one_le_half
  have hpos : (0:ℝ) < 1 - Real.exp (-1) := by
    have := Real.exp_pos (-1)
    linarith
  rw [inv_eq_one_div, div_le_iff₀ hpos]
  linarith

/-- At the witness rate the rooted geometric constant is nonnegative. -/
theorem appendixFHoleRootSumConstant_witness_nonneg (d : ℕ) :
    0 ≤ appendixFHoleRootSumConstant d (appendixFWitnessKappa0 d) := by
  unfold appendixFHoleRootSumConstant
  rw [appendixFWitnessKappa0_geometric_eq]
  have hpos : (0:ℝ) < 1 - Real.exp (-1) := by
    have h := exp_neg_one_le_half
    linarith
  positivity

/-- At the witness rate the transparent moment envelope is at most `2`. -/
theorem appendixFSecondUrsellMomentConstant_witness_le_two (d : ℕ) :
    appendixFSecondUrsellMomentConstant d (appendixFWitnessKappa0 d) ≤ 2 := by
  unfold appendixFSecondUrsellMomentConstant
  refine max_le (by norm_num) (max_le ?_ ?_)
  · have h1 : 1 ≤ appendixFWitnessKappa0 d := one_le_appendixFWitnessKappa0 d
    have hpos : 0 < appendixFWitnessKappa0 d := appendixFWitnessKappa0_pos d
    have : (appendixFWitnessKappa0 d)⁻¹ ≤ 1 := by
      rw [inv_le_one_iff₀]
      right
      exact h1
    linarith
  · exact appendixFHoleRootSumConstant_witness_le_two d

/-- At the witness rate the second-Ursell leaf constant is at most `16`. -/
theorem appendixFSecondUrsellLeafConstant_witness_le (d : ℕ) :
    appendixFSecondUrsellLeafConstant d (appendixFWitnessKappa0 d) ≤ 16 := by
  unfold appendixFSecondUrsellLeafConstant
  have hle : appendixFSecondUrsellMomentConstant d (appendixFWitnessKappa0 d) ≤ 2 :=
    appendixFSecondUrsellMomentConstant_witness_le_two d
  have h1 : (1:ℝ) ≤ appendixFSecondUrsellMomentConstant d (appendixFWitnessKappa0 d) :=
    appendixFSecondUrsellMomentConstant_one_le d _
  nlinarith

/-- **The (O2) joint parameter witness.**  The scalar side conditions of the
composed Appendix-F conditional chain — positivity, the `κ ≥ 4κ₀ + 3` rate
margin, the amplitude window, geometric smallness, and the second-Ursell
half-budget — are JOINTLY satisfiable, at the explicit point
`κ₀ = κ₀(d)`, `κ = 4κ₀ + 3`, `H₀ = 1/256`, with a factor-2 margin in the
half-budget.  The parameter region of the chain is non-empty (house rule 3:
the conditional theorems are not vacuously quantified over an empty regime). -/
theorem appendixF_kappaBudget_witness (d : ℕ) :
    ∃ κ₀ κ H₀ : ℝ, 0 < κ₀ ∧ 4 * κ₀ + 3 ≤ κ ∧ 0 ≤ H₀ ∧ H₀ ≤ 1 ∧
      ((3 ^ d : ℕ) : ℝ) ^ 2 * (Real.exp (-κ₀) * 2 ^ (3 ^ d + 1)) < 1 ∧
      appendixFSecondUrsellLeafConstant d κ₀ *
        (2 * H₀ * appendixFHoleRootSumConstant d κ₀) ≤ 1 / 2 := by
  refine ⟨appendixFWitnessKappa0 d, 4 * appendixFWitnessKappa0 d + 3, 1 / 256,
    appendixFWitnessKappa0_pos d, le_refl _, by norm_num, by norm_num,
    appendixFWitnessKappa0_geometric_lt_one d, ?_⟩
  have hleaf : appendixFSecondUrsellLeafConstant d (appendixFWitnessKappa0 d) ≤ 16 :=
    appendixFSecondUrsellLeafConstant_witness_le d
  have hleaf0 : (0:ℝ) ≤ appendixFSecondUrsellLeafConstant d (appendixFWitnessKappa0 d) := by
    unfold appendixFSecondUrsellLeafConstant
    positivity
  have hroot : appendixFHoleRootSumConstant d (appendixFWitnessKappa0 d) ≤ 2 :=
    appendixFHoleRootSumConstant_witness_le_two d
  have hroot0 : 0 ≤ appendixFHoleRootSumConstant d (appendixFWitnessKappa0 d) :=
    appendixFHoleRootSumConstant_witness_nonneg d
  nlinarith

/-- **The θ-shifted residual budget (consumed by ladder brick B3).**  Paying
the B2 cardinality-tilt `θ` out of the residual rate at the shifted margin
`κ = 4κ₀ + 3 + θ` leaves exactly the summability rate `κ₀`:
`polymerClusterResidualRate (4κ₀+3+θ) κ₀ − θ = κ₀`. -/
theorem appendixF_thetaShifted_residual_budget (κ₀ θ : ℝ) :
    polymerClusterResidualRate (4 * κ₀ + 3 + θ) κ₀ - θ = κ₀ := by
  unfold polymerClusterResidualRate
  ring

end YangMills.RG
