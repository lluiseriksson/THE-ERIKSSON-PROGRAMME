/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP98CauchyLayerIdentity
import Mathlib.Analysis.Normed.Ring.InfiniteSum

/-!
# The exact left-trivialized exponential derivative in CMP98

This module passes from the finite homogeneous identity to the absolutely
convergent Cauchy product and proves the source formula

`exp(-Y) * D exp(Y)[H] = g(ad Y)[H]`.

The proof never cancels `ad Y`, which need not be injective.
-/

namespace YangMills.RG

open scoped BigOperators RightActions

noncomputable section

variable {𝔸 : Type*}
variable [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]

/-- Left multiplication has operator norm at most the norm of its factor. -/
theorem norm_cmp98LeftMulCLM_le (Y : 𝔸) :
    ‖cmp98LeftMulCLM Y‖ ≤ ‖Y‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg Y)
  intro H
  simpa using norm_mul_le Y H

/-- Powers of left multiplication retain the sharp elementary norm bound,
including degree zero where only `norm_id_le` is available. -/
theorem norm_cmp98LeftMulCLM_pow_le (Y : 𝔸) (r : ℕ) :
    ‖cmp98LeftMulCLM Y ^ r‖ ≤ ‖Y‖ ^ r := by
  induction r with
  | zero =>
      simpa using (ContinuousLinearMap.norm_id_le :
        ‖ContinuousLinearMap.id ℝ 𝔸‖ ≤ 1)
  | succ r ih =>
      rw [pow_succ, pow_succ]
      exact (norm_mul_le _ _).trans (mul_le_mul ih
        (norm_cmp98LeftMulCLM_le Y) (norm_nonneg _) (by positivity))

/-- Exponential majorant for the negative left-exponential terms. -/
theorem norm_cmp98NegLeftExpTerm_le (Y : 𝔸) (r : ℕ) :
    ‖cmp98NegLeftExpTerm Y r‖ ≤ ‖Y‖ ^ r / r.factorial := by
  rw [cmp98NegLeftExpTerm, norm_smul, Real.norm_eq_abs]
  have hfac : 0 ≤ (r.factorial : ℝ) := by positivity
  rw [abs_div, abs_pow, abs_neg, abs_one, one_pow,
    abs_of_nonneg hfac]
  calc
    1 / (r.factorial : ℝ) * ‖cmp98LeftMulCLM Y ^ r‖ ≤
        1 / (r.factorial : ℝ) * ‖Y‖ ^ r := by
      gcongr
      exact norm_cmp98LeftMulCLM_pow_le Y r
    _ = ‖Y‖ ^ r / r.factorial := by
      rw [div_eq_mul_inv, div_eq_mul_inv]
      ring

/-- Absolute summability of the negative left-exponential series. -/
theorem summable_norm_cmp98NegLeftExpTerm (Y : 𝔸) :
    Summable (fun r : ℕ => ‖cmp98NegLeftExpTerm Y r‖) := by
  exact (Real.summable_pow_div_factorial ‖Y‖).of_nonneg_of_le
    (fun _ => norm_nonneg _) (fun r => norm_cmp98NegLeftExpTerm_le Y r)

/-- Pointwise form of a negative left-exponential term. -/
theorem cmp98NegLeftExpTerm_apply_eq (Y H : 𝔸) (r : ℕ) :
    cmp98NegLeftExpTerm Y r H =
      ((r.factorial : ℝ)⁻¹) • ((-Y) ^ r * H) := by
  have hnegpow : (-Y) ^ r = ((-1 : ℝ) ^ r) • Y ^ r := by
    induction r with
    | zero => simp
    | succ r ih =>
        rw [pow_succ, pow_succ, ih]
        simp [pow_succ]
  rw [cmp98NegLeftExpTerm, ContinuousLinearMap.smul_apply,
    cmp98LeftMulCLM_pow_apply]
  rw [hnegpow, smul_mul_assoc, smul_smul]
  congr 1
  ring

/-- The operator sum of the negative left-exponential terms is literal
left multiplication by `exp(-Y)`. -/
theorem tsum_cmp98NegLeftExpTerm_eq (Y : 𝔸) :
    (∑' r : ℕ, cmp98NegLeftExpTerm Y r) =
      cmp98LeftMulCLM (NormedSpace.exp (-Y)) := by
  ext H
  let evalH : (𝔸 →L[ℝ] 𝔸) →L[ℝ] 𝔸 :=
    ContinuousLinearMap.apply ℝ 𝔸 H
  calc
    (∑' r : ℕ, cmp98NegLeftExpTerm Y r) H =
        ∑' r : ℕ, cmp98NegLeftExpTerm Y r H := by
      exact evalH.map_tsum (summable_norm_cmp98NegLeftExpTerm Y).of_norm
    _ = ∑' r : ℕ, ((r.factorial : ℝ)⁻¹) • ((-Y) ^ r * H) := by
      apply tsum_congr
      intro r
      exact cmp98NegLeftExpTerm_apply_eq Y H r
    _ = NormedSpace.exp (-Y) * H :=
      (hasSum_exp_pow_mul_right (-Y) H).tsum_eq
    _ = cmp98LeftMulCLM (NormedSpace.exp (-Y)) H := by simp

/-- Absolute summability of the ordered derivative terms in operator norm. -/
theorem summable_norm_expTermFDeriv [NormOneClass 𝔸] (Y : 𝔸) :
    Summable (fun n : ℕ => ‖expTermFDeriv Y n‖) := by
  exact (summable_natCast_div_factorial_mul_pow_pred ‖Y‖).of_nonneg_of_le
    (fun _ => norm_nonneg _) (fun n => norm_expTermFDeriv_le Y n)

/-- Absolute summability after deleting the zero derivative term. -/
theorem summable_norm_expTermFDeriv_shift [NormOneClass 𝔸] (Y : 𝔸) :
    Summable (fun n : ℕ => ‖expTermFDeriv Y (n + 1)‖) := by
  exact (summable_norm_expTermFDeriv Y).comp_injective
    (fun _ _ h => Nat.add_right_cancel h)

/-- Deleting the zero term leaves the derivative series unchanged. -/
theorem tsum_expTermFDeriv_shift_eq_fderiv [NormOneClass 𝔸] (Y : 𝔸) :
    (∑' n : ℕ, expTermFDeriv Y (n + 1)) =
      fderiv ℝ (NormedSpace.exp : 𝔸 → 𝔸) Y := by
  rw [fderiv_exp_eq_ordered]
  have hs := summable_expTermFDeriv Y
  simpa [expTermFDeriv] using hs.sum_add_tsum_nat_add 1

/-- Absolute Cauchy multiplication followed by the homogeneous identity. -/
theorem tsum_negLeft_mul_tsum_expFDeriv_shift_eq_gad
    [NormOneClass 𝔸] (Y : 𝔸) :
    ((∑' r : ℕ, cmp98NegLeftExpTerm Y r) *
        ∑' n : ℕ, expTermFDeriv Y (n + 1)) = cmp98GAd Y := by
  calc
    ((∑' r : ℕ, cmp98NegLeftExpTerm Y r) *
        ∑' n : ℕ, expTermFDeriv Y (n + 1)) =
        ∑' N : ℕ, cmp98LeftTrivializedCauchyLayer Y N := by
      simpa [cmp98LeftTrivializedCauchyLayer] using
        (tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm
          (summable_norm_cmp98NegLeftExpTerm Y)
          (summable_norm_expTermFDeriv_shift Y))
    _ = ∑' N : ℕ, cmp98GAdTerm Y N := by
      apply tsum_congr
      intro N
      exact cmp98LeftTrivializedCauchyLayer_eq_gadTerm Y N
    _ = cmp98GAd Y := by rfl

/- **CMP98 (32)--(33), exact source identity.**  The left-trivialized
Fréchet derivative of the noncommutative exponential is Balaban's entire
operator `g(ad Y)`. -/
theorem cmp98_leftTrivialized_fderiv_exp_eq_gad
    [NormOneClass 𝔸] (Y : 𝔸) :
    cmp98LeftMulCLM (NormedSpace.exp (-Y)) *
        fderiv ℝ (NormedSpace.exp : 𝔸 → 𝔸) Y = cmp98GAd Y := by
  rw [← tsum_cmp98NegLeftExpTerm_eq Y,
    ← tsum_expTermFDeriv_shift_eq_fderiv Y]
  exact tsum_negLeft_mul_tsum_expFDeriv_shift_eq_gad Y

/-- Pointwise form of the exact CMP98 left-trivialized derivative. -/
theorem cmp98_exp_neg_mul_fderiv_exp_eq_gad_apply
    [NormOneClass 𝔸] (Y H : 𝔸) :
    NormedSpace.exp (-Y) *
        fderiv ℝ (NormedSpace.exp : 𝔸 → 𝔸) Y H = cmp98GAd Y H := by
  have h := congrArg (fun T : 𝔸 →L[ℝ] 𝔸 => T H)
    (cmp98_leftTrivialized_fderiv_exp_eq_gad Y)
  simpa using h

end

end YangMills.RG
