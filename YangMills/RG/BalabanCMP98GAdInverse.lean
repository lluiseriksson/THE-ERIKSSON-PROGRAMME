/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP98GAdSeries
import YangMills.RG.BalabanCMP99PatchedParametrixNeumann

/-!
# Certified inverse of the CMP98 `g(ad)` operator

The three correction lines in CMP98 (124) contain `g(ad Y)⁻¹`.  This file
does not introduce that inverse as an unconstrained symbol.  It constructs it
as the convergent Neumann inverse of `g(ad Y) = 1 + D` and proves both inverse
identities under the visible contraction condition `‖D‖ < 1`.
-/

namespace YangMills.RG

noncomputable section

variable {𝔸 : Type*}
variable [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]

/-- Neumann construction of the inverse operator printed as `g(ad Y)⁻¹`. -/
noncomputable def cmp98GAdInv (Y : 𝔸) : 𝔸 →L[ℝ] 𝔸 :=
  cmp99PatchedDefectNeumannInverse
    (cmp98GAd Y - ContinuousLinearMap.id ℝ 𝔸)

/-- Removing the constant term of `g(ad Y)` leaves exactly its positive-degree
tail. -/
theorem cmp98GAd_sub_id_eq_tsum_succ (Y : 𝔸) :
    cmp98GAd Y - ContinuousLinearMap.id ℝ 𝔸 =
      ∑' n : ℕ, cmp98GAdTerm Y (n + 1) := by
  rw [cmp98GAd, (summable_cmp98GAdTerm Y).tsum_eq_zero_add,
    cmp98GAdTerm_zero]
  abel

/-- Explicit exponential bound for the nonconstant `g(ad Y)` tail. -/
theorem norm_cmp98GAd_sub_id_le_exp_sub_one (Y : 𝔸) :
    ‖cmp98GAd Y - ContinuousLinearMap.id ℝ 𝔸‖ ≤
      Real.exp (2 * ‖Y‖) - 1 := by
  rw [cmp98GAd_sub_id_eq_tsum_succ]
  have hsum : Summable (fun n : ℕ => cmp98GAdTerm Y (n + 1)) :=
    (summable_cmp98GAdTerm Y).comp_injective Nat.succ_injective
  have hmajor : Summable (fun n : ℕ =>
      (2 * ‖Y‖) ^ (n + 1) / (n + 1).factorial) :=
    (Real.summable_pow_div_factorial (2 * ‖Y‖)).comp_injective
      Nat.succ_injective
  have hsumNorm : Summable (fun n : ℕ =>
      ‖cmp98GAdTerm Y (n + 1)‖) :=
    hmajor.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun n => norm_cmp98GAdTerm_le Y (n + 1))
  have hmajor_tsum :
      (∑' n : ℕ, (2 * ‖Y‖) ^ (n + 1) / (n + 1).factorial) =
        Real.exp (2 * ‖Y‖) - 1 := by
    have hfull :
        (∑' n : ℕ, (2 * ‖Y‖) ^ n / (n.factorial : ℝ)) =
          Real.exp (2 * ‖Y‖) := by
      rw [Real.exp_eq_exp_ℝ]
      exact (congrFun NormedSpace.exp_eq_tsum_div (2 * ‖Y‖)).symm
    have hsplit :=
      (Real.summable_pow_div_factorial (2 * ‖Y‖)).tsum_eq_zero_add
    rw [hfull] at hsplit
    norm_num at hsplit ⊢
    linarith
  calc
    ‖∑' n : ℕ, cmp98GAdTerm Y (n + 1)‖ ≤
        ∑' n : ℕ, ‖cmp98GAdTerm Y (n + 1)‖ :=
      norm_tsum_le_tsum_norm hsumNorm
    _ ≤ ∑' n : ℕ,
        (2 * ‖Y‖) ^ (n + 1) / (n + 1).factorial :=
      hsumNorm.tsum_le_tsum
        (fun n => norm_cmp98GAdTerm_le Y (n + 1)) hmajor
    _ = Real.exp (2 * ‖Y‖) - 1 :=
      hmajor_tsum

/-- A direct source-scale smallness condition which guarantees that the
Neumann inverse exists. -/
theorem norm_cmp98GAd_sub_id_lt_one_of_exp_lt_two
    (Y : 𝔸) (hY : Real.exp (2 * ‖Y‖) < 2) :
    ‖cmp98GAd Y - ContinuousLinearMap.id ℝ 𝔸‖ < 1 := by
  exact lt_of_le_of_lt (norm_cmp98GAd_sub_id_le_exp_sub_one Y) (by linarith)

/-- `g(ad Y)` composed with its certified inverse is the identity. -/
theorem cmp98GAd_comp_cmp98GAdInv
    (Y : 𝔸)
    (hsmall : ‖cmp98GAd Y - ContinuousLinearMap.id ℝ 𝔸‖ < 1) :
    (cmp98GAd Y).comp (cmp98GAdInv Y) =
      ContinuousLinearMap.id ℝ 𝔸 := by
  have hdecomp :
      ContinuousLinearMap.id ℝ 𝔸 +
          (cmp98GAd Y - ContinuousLinearMap.id ℝ 𝔸) =
        cmp98GAd Y := by abel
  calc
    (cmp98GAd Y).comp (cmp98GAdInv Y) =
        (ContinuousLinearMap.id ℝ 𝔸 +
          (cmp98GAd Y - ContinuousLinearMap.id ℝ 𝔸)).comp
            (cmp98GAdInv Y) := by rw [hdecomp]
    _ = ContinuousLinearMap.id ℝ 𝔸 := by
      unfold cmp98GAdInv
      exact one_add_comp_cmp99PatchedDefectNeumannInverse _ hsmall

/-- The same Neumann construction is also a left inverse. -/
theorem cmp98GAdInv_comp_cmp98GAd
    (Y : 𝔸)
    (hsmall : ‖cmp98GAd Y - ContinuousLinearMap.id ℝ 𝔸‖ < 1) :
    (cmp98GAdInv Y).comp (cmp98GAd Y) =
      ContinuousLinearMap.id ℝ 𝔸 := by
  have hdecomp :
      ContinuousLinearMap.id ℝ 𝔸 +
          (cmp98GAd Y - ContinuousLinearMap.id ℝ 𝔸) =
        cmp98GAd Y := by abel
  calc
    (cmp98GAdInv Y).comp (cmp98GAd Y) =
        (cmp98GAdInv Y).comp
          (ContinuousLinearMap.id ℝ 𝔸 +
            (cmp98GAd Y - ContinuousLinearMap.id ℝ 𝔸)) := by rw [hdecomp]
    _ = ContinuousLinearMap.id ℝ 𝔸 := by
      unfold cmp98GAdInv
      exact cmp99PatchedDefectNeumannInverse_comp_one_add _ hsmall

/-- Pointwise right-inverse identity used in the source regrouping. -/
theorem cmp98GAd_cmp98GAdInv_apply
    (Y H : 𝔸)
    (hsmall : ‖cmp98GAd Y - ContinuousLinearMap.id ℝ 𝔸‖ < 1) :
    cmp98GAd Y (cmp98GAdInv Y H) = H := by
  have h := congrArg (fun T : 𝔸 →L[ℝ] 𝔸 => T H)
    (cmp98GAd_comp_cmp98GAdInv Y hsmall)
  simpa using h

/-- Pointwise left-inverse identity used in the source regrouping. -/
theorem cmp98GAdInv_cmp98GAd_apply
    (Y H : 𝔸)
    (hsmall : ‖cmp98GAd Y - ContinuousLinearMap.id ℝ 𝔸‖ < 1) :
    cmp98GAdInv Y (cmp98GAd Y H) = H := by
  have h := congrArg (fun T : 𝔸 →L[ℝ] 𝔸 => T H)
    (cmp98GAdInv_comp_cmp98GAd Y hsmall)
  simpa using h

/-- Right-inverse identity with the operator contraction discharged from the
explicit exponential smallness of the Lie-algebra background. -/
theorem cmp98GAd_cmp98GAdInv_apply_of_exp_lt_two
    (Y H : 𝔸) (hY : Real.exp (2 * ‖Y‖) < 2) :
    cmp98GAd Y (cmp98GAdInv Y H) = H :=
  cmp98GAd_cmp98GAdInv_apply Y H
    (norm_cmp98GAd_sub_id_lt_one_of_exp_lt_two Y hY)

/-- Left-inverse identity under the same explicit background smallness. -/
theorem cmp98GAdInv_cmp98GAd_apply_of_exp_lt_two
    (Y H : 𝔸) (hY : Real.exp (2 * ‖Y‖) < 2) :
    cmp98GAdInv Y (cmp98GAd Y H) = H :=
  cmp98GAdInv_cmp98GAd_apply Y H
    (norm_cmp98GAd_sub_id_lt_one_of_exp_lt_two Y hY)

end

end YangMills.RG
