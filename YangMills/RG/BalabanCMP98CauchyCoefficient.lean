/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP98TriangleReindex

/-!
# Cauchy-layer coefficients for the CMP98 exponential identity

After triangular reindexing, the coefficient of the two-sided monomial
`Y^(N-b) H Y^b` is the finite convolution of the negative exponential
with the shifted derivative series.  This file identifies that scalar
coefficient exactly with the coefficient in `g(ad Y)`.
-/

namespace YangMills.RG

open scoped BigOperators

/-- Exact coefficient of the `b`-th two-sided monomial in Cauchy layer
`N` of `exp(-L_Y) * D exp_Y`. -/
theorem cmp98_leftTrivialized_cauchy_coefficient
    (N b : ℕ) (hb : b < N + 1) :
    (∑ r ∈ Finset.range (N - b + 1),
        ((-1 : ℝ) ^ r) /
          (((r.factorial : ℝ) * ((N - r + 1).factorial : ℝ)))) =
      ((-1 : ℝ) ^ (N - b)) /
        ((((N - b).factorial : ℝ) * (b.factorial : ℝ)) * (N + 1)) := by
  have hle : b ≤ N := by omega
  let a := N - b
  have hNa : a + b = N := by
    dsimp [a]
    omega
  calc
    (∑ r ∈ Finset.range (N - b + 1),
        ((-1 : ℝ) ^ r) /
          (((r.factorial : ℝ) * ((N - r + 1).factorial : ℝ)))) =
        ∑ i ∈ Finset.range (a + 1),
          ((-1 : ℝ) ^ (a - i)) /
            ((((a - i).factorial : ℝ) *
              ((N - (a - i) + 1).factorial : ℝ))) := by
      have href := Finset.sum_range_reflect
        (fun r => ((-1 : ℝ) ^ r) /
          (((r.factorial : ℝ) * ((N - r + 1).factorial : ℝ)))) (a + 1)
      simpa [a] using href.symm
    _ = ∑ i ∈ Finset.range (a + 1),
          ((-1 : ℝ) ^ (a - i)) /
            ((((a - i).factorial : ℝ) *
              ((i + b + 1).factorial : ℝ))) := by
      apply Finset.sum_congr rfl
      intro i hi
      have hilt : i < a + 1 := Finset.mem_range.mp hi
      have hidx : N - (a - i) + 1 = i + b + 1 := by omega
      rw [hidx]
    _ = ((-1 : ℝ) ^ a) /
          (((a.factorial : ℝ) * (b.factorial : ℝ)) * (a + b + 1)) :=
      cmp98_exp_deriv_convolution_coefficient a b
    _ = ((-1 : ℝ) ^ (N - b)) /
          ((((N - b).factorial : ℝ) * (b.factorial : ℝ)) * (N + 1)) := by
      dsimp [a]
      rw [← Nat.cast_add, hNa]

end YangMills.RG
