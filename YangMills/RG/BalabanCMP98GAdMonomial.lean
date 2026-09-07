/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP98GAdCoefficient

/-!
# Homogeneous monomials in the CMP98 `g(ad Y)` series

This module expands each homogeneous commutator power into the common
two-sided monomial basis used by the left-trivialized exponential
derivative.  The coefficient is proved from factorial identities rather
than inferred by cancelling the commutator.
-/

namespace YangMills.RG

open scoped BigOperators RightActions

noncomputable section

/-- Scalar coefficient of the `m`-th binomial monomial in the `n`-th
homogeneous term of `g(ad Y)`. -/
theorem cmp98_gad_binomial_coefficient (n m : ℕ) (hm : m < n + 1) :
    (((-1 : ℝ) ^ n) / (n + 1).factorial) *
        (((-1 : ℝ) ^ (n - m)) * (n.choose m : ℝ)) =
      ((-1 : ℝ) ^ m) /
        (((m.factorial : ℝ) * ((n - m).factorial : ℝ)) * (n + 1)) := by
  have hmn : m ≤ n := by omega
  rw [Nat.cast_choose ℝ hmn, Nat.factorial_succ]
  have hmfac : (m.factorial : ℝ) ≠ 0 := by positivity
  have hsubfac : ((n - m).factorial : ℝ) ≠ 0 := by positivity
  have hnfac : (n.factorial : ℝ) ≠ 0 := by positivity
  have hsucc : (n + 1 : ℝ) ≠ 0 := by positivity
  field_simp
  push_cast
  rw [← pow_add]
  have hsum : n + (n - m) = m + 2 * (n - m) := by omega
  rw [hsum, pow_add, pow_mul]
  norm_num
  ring

variable {𝔸 : Type*}
variable [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]

/-- A power of negative right multiplication, evaluated pointwise. -/
theorem neg_cmp98RightMulCLM_pow_apply (Y H : 𝔸) (n : ℕ) :
    ((-cmp98RightMulCLM Y) ^ n) H =
      ((-1 : ℝ) ^ n) • (H * Y ^ n) := by
  induction n generalizing H with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, ContinuousLinearMap.mul_apply, ih]
      simp only [ContinuousLinearMap.neg_apply,
        cmp98RightMulCLM_apply, pow_succ']
      simp [mul_assoc]

/-- The common two-sided monomial in total degree `n`. -/
def cmp98GAdMonomial (Y : 𝔸) (n m : ℕ) : 𝔸 →L[ℝ] 𝔸 :=
  (((-1 : ℝ) ^ m) /
      (((m.factorial : ℝ) * ((n - m).factorial : ℝ)) * (n + 1))) •
    ((cmp98LeftMulCLM Y) ^ m * (cmp98RightMulCLM Y) ^ (n - m))

/-- Pointwise evaluation of a common two-sided monomial. -/
theorem cmp98GAdMonomial_apply (Y H : 𝔸) (n m : ℕ) :
    cmp98GAdMonomial Y n m H =
      (((-1 : ℝ) ^ m) /
        (((m.factorial : ℝ) * ((n - m).factorial : ℝ)) * (n + 1))) •
          (Y ^ m * H * Y ^ (n - m)) := by
  rw [cmp98GAdMonomial, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.mul_apply, cmp98RightMulCLM_pow_apply,
    cmp98LeftMulCLM_pow_apply]
  congr 1
  exact (mul_assoc _ _ _).symm

/-- Each homogeneous term of `g(ad Y)` is exactly the finite sum of its
two-sided monomials. -/
theorem cmp98GAdTerm_eq_sum_monomial (Y : 𝔸) (n : ℕ) :
    cmp98GAdTerm Y n =
      ∑ m ∈ Finset.range (n + 1), cmp98GAdMonomial Y n m := by
  ext H
  rw [cmp98GAdTerm_apply, cmp98AdCLM_pow_apply_eq_binomial]
  rw [ContinuousLinearMap.sum_apply, ContinuousLinearMap.sum_apply,
    Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  rw [ContinuousLinearMap.mul_apply, ContinuousLinearMap.mul_apply,
    neg_cmp98RightMulCLM_pow_apply, cmp98LeftMulCLM_pow_apply,
    cmp98GAdMonomial_apply]
  have hchoose :
      (((n.choose m : ℕ) : 𝔸 →L[ℝ] 𝔸) H) =
        (n.choose m : ℝ) • H := by
    rw [ContinuousLinearMap.natCast_apply, Nat.cast_smul_eq_nsmul]
  rw [hchoose]
  have hcoeff := cmp98_gad_binomial_coefficient n m (Finset.mem_range.mp hm)
  rw [← hcoeff]
  simp [smul_smul, mul_assoc]

/-- The homogeneous two-sided expansion is absolutely summable. -/
theorem summable_cmp98GAd_sum_monomial (Y : 𝔸) :
    Summable (fun n : ℕ =>
      ∑ m ∈ Finset.range (n + 1), cmp98GAdMonomial Y n m) := by
  simpa only [← cmp98GAdTerm_eq_sum_monomial] using
    summable_cmp98GAdTerm Y

/-- `g(ad Y)` as the absolutely convergent sum of its common two-sided
homogeneous monomials. -/
theorem cmp98GAd_eq_tsum_sum_monomial (Y : 𝔸) :
    cmp98GAd Y =
      ∑' n : ℕ, ∑ m ∈ Finset.range (n + 1),
        cmp98GAdMonomial Y n m := by
  unfold cmp98GAd
  apply tsum_congr
  intro n
  exact cmp98GAdTerm_eq_sum_monomial Y n

end

end YangMills.RG
