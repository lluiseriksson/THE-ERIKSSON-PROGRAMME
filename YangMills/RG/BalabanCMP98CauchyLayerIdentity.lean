/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP98CauchyLayer

/-!
# Identification of CMP98 Cauchy layers with `g(ad Y)`

The finite triangular sum is reindexed by the right exponent, its scalar
coefficient is evaluated exactly, and the outer order is reflected back to
the left exponent used by `cmp98GAdMonomial`.  No infinite-series
interchange occurs in this module.
-/

namespace YangMills.RG

open scoped BigOperators RightActions

noncomputable section

variable {𝔸 : Type*}
variable [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]

/-- One homogeneous Cauchy layer of `exp(-L_Y) * D exp_Y` is exactly the
corresponding homogeneous term of `g(ad Y)`. -/
theorem cmp98LeftTrivializedCauchyLayer_eq_gadTerm
    (Y : 𝔸) (N : ℕ) :
    cmp98LeftTrivializedCauchyLayer Y N = cmp98GAdTerm Y N := by
  ext H
  rw [cmp98LeftTrivializedCauchyLayer_apply_eq_triangle]
  rw [sum_range_triangle_comm]
  have hinner (b : ℕ) (hb : b ∈ Finset.range (N + 1)) :
      (∑ r ∈ Finset.range (N - b + 1),
          (((-1 : ℝ) ^ r) /
            (((r.factorial : ℝ) * ((N - r + 1).factorial : ℝ)))) •
              (Y ^ (N - b) * H * Y ^ b)) =
        cmp98GAdMonomial Y N (N - b) H := by
    have hblt : b < N + 1 := Finset.mem_range.mp hb
    have hble : b ≤ N := by omega
    rw [← Finset.sum_smul]
    rw [cmp98_leftTrivialized_cauchy_coefficient N b hblt]
    rw [cmp98GAdMonomial_apply]
    have hsub : N - (N - b) = b := by omega
    rw [hsub]
  calc
    (∑ b ∈ Finset.range (N + 1),
        ∑ r ∈ Finset.range (N - b + 1),
          (((-1 : ℝ) ^ r) /
            (((r.factorial : ℝ) * ((N - r + 1).factorial : ℝ)))) •
              (Y ^ (N - b) * H * Y ^ b)) =
        ∑ b ∈ Finset.range (N + 1),
          cmp98GAdMonomial Y N (N - b) H := by
      apply Finset.sum_congr rfl
      intro b hb
      exact hinner b hb
    _ = ∑ m ∈ Finset.range (N + 1), cmp98GAdMonomial Y N m H := by
      simpa using (Finset.sum_range_reflect
        (fun m => cmp98GAdMonomial Y N m H) (N + 1))
    _ = cmp98GAdTerm Y N H := by
      rw [cmp98GAdTerm_eq_sum_monomial,
        ContinuousLinearMap.sum_apply]

end

end YangMills.RG
