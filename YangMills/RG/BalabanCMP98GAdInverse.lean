/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP98GAdSeries
import YangMills.RG.BalabanCMP99PatchedParametrixNeumann
import Mathlib.Analysis.Complex.ExponentialBounds

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

/-- Sharp shifted-factorial majorant for a `g(ad Y)` coefficient.  Unlike
`norm_cmp98GAdTerm_le`, this retains the source denominator `(n+1)!`. -/
theorem norm_cmp98GAdTerm_le_succFactorial (Y : 𝔸) (n : ℕ) :
    ‖cmp98GAdTerm Y n‖ ≤
      (2 * ‖Y‖) ^ n / (n + 1).factorial := by
  rcases n with _ | n
  · simpa [cmp98GAdTerm] using
      (ContinuousLinearMap.norm_id_le :
        ‖ContinuousLinearMap.id ℝ 𝔸‖ ≤ 1)
  rw [cmp98GAdTerm, norm_smul, Real.norm_eq_abs]
  have hfac0 : 0 ≤ (((n + 1 + 1).factorial : ℕ) : ℝ) := by positivity
  have hcoeff :
      |((-1 : ℝ) ^ (n + 1)) / (((n + 1 + 1).factorial : ℕ) : ℝ)| =
        ((((n + 1 + 1).factorial : ℕ) : ℝ))⁻¹ := by
    rw [div_eq_mul_inv, abs_mul, abs_pow, abs_neg, abs_one, one_pow,
      one_mul, abs_of_nonneg (inv_nonneg.mpr hfac0)]
  rw [hcoeff]
  calc
    ((((n + 1 + 1).factorial : ℕ) : ℝ))⁻¹ *
        ‖cmp98AdCLM Y ^ (n + 1)‖ ≤
        ((((n + 1 + 1).factorial : ℕ) : ℝ))⁻¹ *
          ‖cmp98AdCLM Y‖ ^ (n + 1) := by
      exact mul_le_mul_of_nonneg_left
        (norm_pow_le' _ (Nat.succ_pos n)) (by positivity)
    _ ≤ ((((n + 1 + 1).factorial : ℕ) : ℝ))⁻¹ *
          (2 * ‖Y‖) ^ (n + 1) := by
      gcongr
      exact norm_cmp98AdCLM_le Y
    _ = (2 * ‖Y‖) ^ (n + 1) / (n + 1 + 1).factorial := by
      rw [div_eq_mul_inv]
      ring

/-- The nonconstant `g(ad Y)` tail retains its shifted exponential
majorant, rather than losing one factorial as in the coarse bound. -/
theorem norm_cmp98GAd_sub_id_le_shiftedTail (Y : 𝔸) :
    ‖cmp98GAd Y - ContinuousLinearMap.id ℝ 𝔸‖ ≤
      ∑' n : ℕ, (2 * ‖Y‖) ^ (n + 1) / (n + 2).factorial := by
  rw [cmp98GAd_sub_id_eq_tsum_succ]
  have htail : Summable (fun n : ℕ => cmp98GAdTerm Y (n + 1)) :=
    (summable_cmp98GAdTerm Y).comp_injective Nat.succ_injective
  have hmajor : Summable (fun n : ℕ =>
      (2 * ‖Y‖) ^ (n + 1) / (n + 2).factorial) := by
    let x : ℝ := 2 * ‖Y‖
    by_cases hx : x = 0
    · simp [x, hx]
    · have hshift : Summable (fun n : ℕ =>
          x ^ (n + 2) / (n + 2).factorial) := by
        simpa [Function.comp_def] using
          (summable_nat_add_iff 2).mpr
            (Real.summable_pow_div_factorial x)
      have hmul := hshift.mul_left x⁻¹
      have heq : (fun n : ℕ => x⁻¹ *
          (x ^ (n + 2) / (n + 2).factorial)) =
          fun n : ℕ => x ^ (n + 1) / (n + 2).factorial := by
        funext n
        rw [show n + 2 = (n + 1) + 1 by omega, pow_succ]
        field_simp
      rw [heq] at hmul
      simpa [x] using hmul
  have hnorm : Summable (fun n : ℕ => ‖cmp98GAdTerm Y (n + 1)‖) :=
    hmajor.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun n => norm_cmp98GAdTerm_le_succFactorial Y (n + 1))
  calc
    ‖∑' n : ℕ, cmp98GAdTerm Y (n + 1)‖ ≤
        ∑' n : ℕ, ‖cmp98GAdTerm Y (n + 1)‖ :=
      norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' n : ℕ,
        (2 * ‖Y‖) ^ (n + 1) / (n + 2).factorial :=
      hnorm.tsum_le_tsum
        (fun n => norm_cmp98GAdTerm_le_succFactorial Y (n + 1)) hmajor

/-- At the source logarithmic radius `1/2`, the shifted tail is bounded by
`e - 2`, strictly below one. -/
theorem norm_cmp98GAd_sub_id_lt_one_of_norm_le_half
    (Y : 𝔸) (hY : ‖Y‖ ≤ 1 / 2) :
    ‖cmp98GAd Y - ContinuousLinearMap.id ℝ 𝔸‖ < 1 := by
  let x : ℝ := 2 * ‖Y‖
  have hx0 : 0 ≤ x := by dsimp [x]; positivity
  have hx1 : x ≤ 1 := by dsimp [x]; linarith
  have hmajor : Summable (fun n : ℕ =>
      x ^ (n + 1) / (n + 2).factorial) := by
    by_cases hxeq : x = 0
    · simp [hxeq]
    · have hshift : Summable (fun n : ℕ =>
          x ^ (n + 2) / (n + 2).factorial) := by
        simpa [Function.comp_def] using
          (summable_nat_add_iff 2).mpr
            (Real.summable_pow_div_factorial x)
      have hmul := hshift.mul_left x⁻¹
      have heq : (fun n : ℕ => x⁻¹ *
          (x ^ (n + 2) / (n + 2).factorial)) =
          fun n : ℕ => x ^ (n + 1) / (n + 2).factorial := by
        funext n
        rw [show n + 2 = (n + 1) + 1 by omega, pow_succ]
        field_simp
      rw [heq] at hmul
      exact hmul
  have hone : Summable (fun n : ℕ =>
      (1 : ℝ) ^ (n + 1) / (n + 2).factorial) := by
    simpa [Function.comp_def] using
      (summable_nat_add_iff 2).mpr
        (Real.summable_pow_div_factorial (1 : ℝ))
  have hle : (∑' n : ℕ, x ^ (n + 1) / (n + 2).factorial) ≤
      ∑' n : ℕ, (1 : ℝ) ^ (n + 1) / (n + 2).factorial := by
    exact hmajor.tsum_le_tsum (fun n => by
      gcongr) hone
  have htailOne :
      (∑' n : ℕ, (1 : ℝ) ^ (n + 1) / (n + 2).factorial) =
        Real.exp 1 - 2 := by
    have hfull :
        (∑' n : ℕ, (1 : ℝ) ^ n / (n.factorial : ℝ)) = Real.exp 1 := by
      rw [Real.exp_eq_exp_ℝ]
      exact (congrFun NormedSpace.exp_eq_tsum_div (1 : ℝ)).symm
    have hsplit :=
      (Real.summable_pow_div_factorial (1 : ℝ)).sum_add_tsum_nat_add 2
    rw [hfull] at hsplit
    norm_num at hsplit ⊢
    linarith
  have hsource := norm_cmp98GAd_sub_id_le_shiftedTail Y
  change ‖cmp98GAd Y - ContinuousLinearMap.id ℝ 𝔸‖ < 1
  calc
    ‖cmp98GAd Y - ContinuousLinearMap.id ℝ 𝔸‖ ≤
        ∑' n : ℕ, x ^ (n + 1) / (n + 2).factorial := by
      simpa [x] using hsource
    _ ≤ Real.exp 1 - 2 := by rw [← htailOne]; exact hle
    _ < 1 := by linarith [Real.exp_one_lt_three]

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

/-- Left-inverse identity at Balaban's printed logarithmic radius `1/2`.
The contraction is generated by the shifted-factorial tail, not supplied as
an extra operator hypothesis. -/
theorem cmp98GAdInv_cmp98GAd_apply_of_norm_le_half
    (Y H : 𝔸) (hY : ‖Y‖ ≤ 1 / 2) :
    cmp98GAdInv Y (cmp98GAd Y H) = H :=
  cmp98GAdInv_cmp98GAd_apply Y H
    (norm_cmp98GAd_sub_id_lt_one_of_norm_le_half Y hY)

end

end YangMills.RG
