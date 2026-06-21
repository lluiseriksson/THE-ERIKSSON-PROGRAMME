/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.AppendixFSecondUrsellLeafSummation

/-!
# Appendix F second-Ursell denominator closure

This module isolates the elementary real algebra that closes the denominator
side of the source-facing second-Ursell leaf-summation endpoint.  A half-budget
on the leaf constant simultaneously supplies:

* the raw smallness `2 * A * K ≤ 1`,
* the strict geometric denominator condition
  `appendixFSecondUrsellLeafConstant d κ₀ * (2 * A * K) < 1`, and
* the closed denominator bound used by the `H#` consumers.

No source theorem, raw activity estimate, measure-theory statement, or
Yang--Mills model identification is introduced here.

Oracle target: `[propext, Classical.choice, Quot.sound]`. No sorry, no axioms.
-/

attribute [local instance] Classical.propDecidable

namespace YangMills.RG

/-- The leaf constant is at least one. -/
theorem appendixFSecondUrsellLeafConstant_one_le
    (d : ℕ) (κ₀ : ℝ) :
    1 ≤ appendixFSecondUrsellLeafConstant d κ₀ := by
  unfold appendixFSecondUrsellLeafConstant
  have hM : 1 ≤ appendixFSecondUrsellMomentConstant d κ₀ :=
    appendixFSecondUrsellMomentConstant_one_le d κ₀
  nlinarith [sq_nonneg (appendixFSecondUrsellMomentConstant d κ₀)]

/-- The moment constant is bounded by the leaf constant. -/
theorem appendixFSecondUrsellMomentConstant_le_leafConstant
    (d : ℕ) (κ₀ : ℝ) :
    appendixFSecondUrsellMomentConstant d κ₀ ≤
      appendixFSecondUrsellLeafConstant d κ₀ := by
  unfold appendixFSecondUrsellLeafConstant
  have hM : 1 ≤ appendixFSecondUrsellMomentConstant d κ₀ :=
    appendixFSecondUrsellMomentConstant_one_le d κ₀
  nlinarith [sq_nonneg (appendixFSecondUrsellMomentConstant d κ₀)]

/-- If `x` spends at most half of the unit budget, the geometric denominator is
bounded by `2`. -/
theorem one_sub_inv_le_two_of_nonneg_of_le_half
    {x : ℝ} (_hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) :
    (1 - x)⁻¹ ≤ 2 := by
  have hden_ge : (1 / 2 : ℝ) ≤ 1 - x := by
    linarith
  have hden_pos : 0 < 1 - x := by
    linarith
  rw [inv_le_iff_one_le_mul₀ hden_pos]
  nlinarith

/-- Sharp half-budget closure for the source-facing second-Ursell denominator.

The half-budget controls the leaf denominator, and the factor `2` from
`(1 - x)⁻¹ ≤ 2` turns the raw `M * (2 * A * K)` numerator into
`4 * M * A * K`. -/
theorem appendixFSecondUrsell_closed_le_four_mul_rawRoot
    {d : ℕ} {κ₀ A K : ℝ}
    (hA : 0 ≤ A)
    (hK : 0 ≤ K)
    (hhalf :
      appendixFSecondUrsellLeafConstant d κ₀ *
          (2 * A * K) ≤ 1 / 2) :
    (appendixFSecondUrsellMomentConstant d κ₀ *
        (2 * A * K)) *
        (1 - appendixFSecondUrsellLeafConstant d κ₀ *
          (2 * A * K))⁻¹
      ≤
    4 * appendixFSecondUrsellMomentConstant d κ₀ * A * K := by
  let M := appendixFSecondUrsellMomentConstant d κ₀
  let L := appendixFSecondUrsellLeafConstant d κ₀
  let x := L * (2 * A * K)
  have hx0 : 0 ≤ x := by
    dsimp [x, L]
    unfold appendixFSecondUrsellLeafConstant
    exact mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _))
      (mul_nonneg (mul_nonneg zero_le_two hA) hK)
  have hinv : (1 - x)⁻¹ ≤ 2 :=
    one_sub_inv_le_two_of_nonneg_of_le_half hx0
      (by simpa [x, L] using hhalf)
  have hfactor0 : 0 ≤ M * (2 * A * K) := by
    dsimp [M]
    exact mul_nonneg (appendixFSecondUrsellMomentConstant_nonneg d κ₀)
      (mul_nonneg (mul_nonneg zero_le_two hA) hK)
  calc
    (M * (2 * A * K)) * (1 - x)⁻¹
        ≤ (M * (2 * A * K)) * 2 := by
          exact mul_le_mul_of_nonneg_left hinv hfactor0
    _ = 4 * M * A * K := by
          ring

/-- A half-budget plus a final profile bound produces the three source
obligations usually passed separately to the leaf-summation endpoint:
`hsmall`, `hρ1`, and `hBclosed`. -/
theorem appendixFSecondUrsell_sourceObligations_of_halfBudget
    {d : ℕ} {κ₀ A K S : ℝ}
    (hA : 0 ≤ A)
    (hK : 0 ≤ K)
    (hhalf :
      appendixFSecondUrsellLeafConstant d κ₀ *
          (2 * A * K) ≤ 1 / 2)
    (hprofile :
      4 * appendixFSecondUrsellMomentConstant d κ₀ * A * K ≤ S) :
    2 * A * K ≤ 1 ∧
    appendixFSecondUrsellLeafConstant d κ₀ *
        (2 * A * K) < 1 ∧
    (appendixFSecondUrsellMomentConstant d κ₀ *
        (2 * A * K)) *
        (1 - appendixFSecondUrsellLeafConstant d κ₀ *
          (2 * A * K))⁻¹ ≤ S := by
  have hAK0 : 0 ≤ 2 * A * K :=
    mul_nonneg (mul_nonneg zero_le_two hA) hK
  have hL1 : 1 ≤ appendixFSecondUrsellLeafConstant d κ₀ :=
    appendixFSecondUrsellLeafConstant_one_le d κ₀
  have hsmall : 2 * A * K ≤ 1 := by
    have hleL :
        2 * A * K ≤
          appendixFSecondUrsellLeafConstant d κ₀ * (2 * A * K) := by
      nlinarith
    linarith
  have hrho :
      appendixFSecondUrsellLeafConstant d κ₀ * (2 * A * K) < 1 := by
    linarith
  have hclosed :=
    appendixFSecondUrsell_closed_le_four_mul_rawRoot
      (d := d) (κ₀ := κ₀) hA hK hhalf
  exact ⟨hsmall, hrho, hclosed.trans hprofile⟩

end YangMills.RG
