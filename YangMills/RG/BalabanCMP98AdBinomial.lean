/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP98GAdSeries
import Mathlib.Data.Nat.Choose.Sum

/-!
# The finite binomial expansion of powers of `ad Y`

Left and right multiplication by the same background commute.  Therefore
each finite power of

`ad Y = L_Y - R_Y`

has an exact noncommutative binomial expansion.  This is the finite
algebraic identity needed before rearranging the absolutely convergent
series in CMP98 (32).
-/

namespace YangMills.RG

open scoped BigOperators RightActions

noncomputable section

variable {𝔸 : Type*}
variable [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]

/-- Continuous left multiplication by `Y`. -/
def cmp98LeftMulCLM (Y : 𝔸) : 𝔸 →L[ℝ] 𝔸 :=
  Y •> ContinuousLinearMap.id ℝ 𝔸

/-- Continuous right multiplication by `Y`. -/
def cmp98RightMulCLM (Y : 𝔸) : 𝔸 →L[ℝ] 𝔸 :=
  ContinuousLinearMap.id ℝ 𝔸 <• Y

@[simp] theorem cmp98LeftMulCLM_apply (Y H : 𝔸) :
    cmp98LeftMulCLM Y H = Y * H := by
  simp [cmp98LeftMulCLM]

@[simp] theorem cmp98RightMulCLM_apply (Y H : 𝔸) :
    cmp98RightMulCLM Y H = H * Y := by
  simp [cmp98RightMulCLM]

theorem cmp98AdCLM_eq_left_sub_right (Y : 𝔸) :
    cmp98AdCLM Y = cmp98LeftMulCLM Y - cmp98RightMulCLM Y := by
  rfl

/-- Associativity is precisely the statement that left and right
multiplication commute as operators. -/
theorem cmp98LeftMulCLM_commute_rightMulCLM (Y : 𝔸) :
    Commute (cmp98LeftMulCLM Y) (cmp98RightMulCLM Y) := by
  apply ContinuousLinearMap.ext
  intro H
  simp [mul_assoc]

/-- Iterated left multiplication is multiplication by `Y^n`. -/
@[simp] theorem cmp98LeftMulCLM_pow_apply (Y H : 𝔸) (n : ℕ) :
    ((cmp98LeftMulCLM Y) ^ n) H = Y ^ n * H := by
  induction n generalizing H with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, ContinuousLinearMap.mul_apply, ih]
      simp [cmp98LeftMulCLM, pow_succ, mul_assoc]

/-- Iterated right multiplication is multiplication by `Y^n`. -/
@[simp] theorem cmp98RightMulCLM_pow_apply (Y H : 𝔸) (n : ℕ) :
    ((cmp98RightMulCLM Y) ^ n) H = H * Y ^ n := by
  induction n generalizing H with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, ContinuousLinearMap.mul_apply, ih]
      simp [cmp98RightMulCLM, pow_succ', mul_assoc]

/-- Operator-level noncommutative binomial theorem for `(ad Y)^n`. -/
theorem cmp98AdCLM_pow_eq_binomial (Y : 𝔸) (n : ℕ) :
    (cmp98AdCLM Y) ^ n =
      ∑ m ∈ Finset.range (n + 1),
        (cmp98LeftMulCLM Y) ^ m *
          (-cmp98RightMulCLM Y) ^ (n - m) * n.choose m := by
  rw [cmp98AdCLM_eq_left_sub_right, sub_eq_add_neg]
  exact
    (cmp98LeftMulCLM_commute_rightMulCLM Y).neg_right.add_pow n

/-- Pointwise form of the finite binomial expansion.  The scalar sign is
kept as the actual operator power `(-R_Y)^(n-m)` here; the next summation
module extracts it while performing the absolutely convergent reindexing. -/
theorem cmp98AdCLM_pow_apply_eq_binomial (Y H : 𝔸) (n : ℕ) :
    ((cmp98AdCLM Y) ^ n) H =
      (∑ m ∈ Finset.range (n + 1),
        (cmp98LeftMulCLM Y) ^ m *
          (-cmp98RightMulCLM Y) ^ (n - m) * n.choose m) H := by
  rw [cmp98AdCLM_pow_eq_binomial]

end

end YangMills.RG
