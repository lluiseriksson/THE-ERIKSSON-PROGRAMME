/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP98CauchyCoefficient

/-!
# Homogeneous Cauchy layers in the CMP98 exponential identity

This file packages the negative left-exponential series and multiplies its
finite Cauchy layers by the shifted ordered derivative series.  Each layer
is expanded in the same two-sided monomial basis as `cmp98GAdTerm`.
-/

namespace YangMills.RG

open scoped BigOperators RightActions

noncomputable section

variable {𝔸 : Type*}
variable [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]

/-- The `r`-th term of the negative exponential of left multiplication. -/
def cmp98NegLeftExpTerm (Y : 𝔸) (r : ℕ) : 𝔸 →L[ℝ] 𝔸 :=
  (((-1 : ℝ) ^ r) / (r.factorial : ℝ)) •
    (cmp98LeftMulCLM Y) ^ r

/-- The homogeneous Cauchy layer of total degree `N` in
`exp(-L_Y) * D exp_Y`. -/
def cmp98LeftTrivializedCauchyLayer (Y : 𝔸) (N : ℕ) : 𝔸 →L[ℝ] 𝔸 :=
  ∑ r ∈ Finset.range (N + 1),
    cmp98NegLeftExpTerm Y r * expTermFDeriv Y (N - r + 1)

/-- Pointwise expansion of one product in a Cauchy layer. -/
theorem cmp98NegLeftExpTerm_mul_expTermFDeriv_apply
    (Y H : 𝔸) (N r : ℕ) (hr : r < N + 1) :
    (cmp98NegLeftExpTerm Y r * expTermFDeriv Y (N - r + 1)) H =
      ∑ b ∈ Finset.range (N - r + 1),
        (((-1 : ℝ) ^ r) /
          (((r.factorial : ℝ) * ((N - r + 1).factorial : ℝ)))) •
            (Y ^ (N - b) * H * Y ^ b) := by
  have hrle : r ≤ N := by omega
  rw [ContinuousLinearMap.mul_apply, cmp98NegLeftExpTerm,
    ContinuousLinearMap.smul_apply, cmp98LeftMulCLM_pow_apply,
    expTermFDeriv_apply]
  rw [mul_smul_comm, smul_smul, Finset.mul_sum, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro b hb
  have hblt : b < N - r + 1 := Finset.mem_range.mp hb
  have hble : b ≤ N - r := by omega
  have hpred : (N - r + 1).pred = N - r := by
    simp only [Nat.pred_succ]
  have hpow : r + (N - r - b) = N - b := by omega
  rw [hpred]
  congr 1
  · field_simp
  · rw [← mul_assoc (Y ^ r) (Y ^ (N - r - b) * H) (Y ^ b),
      ← mul_assoc (Y ^ r) (Y ^ (N - r - b)) H,
      ← pow_add, hpow]

/-- The complete layer as a finite triangular double sum. -/
theorem cmp98LeftTrivializedCauchyLayer_apply_eq_triangle
    (Y H : 𝔸) (N : ℕ) :
    cmp98LeftTrivializedCauchyLayer Y N H =
      ∑ r ∈ Finset.range (N + 1),
        ∑ b ∈ Finset.range (N - r + 1),
          (((-1 : ℝ) ^ r) /
            (((r.factorial : ℝ) * ((N - r + 1).factorial : ℝ)))) •
              (Y ^ (N - b) * H * Y ^ b) := by
  simp only [cmp98LeftTrivializedCauchyLayer,
    ContinuousLinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro r hr
  exact cmp98NegLeftExpTerm_mul_expTermFDeriv_apply
    Y H N r (Finset.mem_range.mp hr)

end

end YangMills.RG
