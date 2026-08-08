/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import Mathlib.Algebra.BigOperators.Ring.Finset
import YangMills.RG.BalabanCMP89Eq251OneDimensionalAliasSeries

/-!
# PRE-VALIDATION: finite-product factorization in CMP89 (2.51)

The source is present, but this module's `.olean` has not yet been materialized
and its declarations have not yet been verified by the Lean compiler.

The final line of CMP89 (2.51) bounds the `d`-dimensional alias sum by the
`d`-th power of one coordinate series.  This module constructs the literal
product weight over `Fin d`, proves the exact finite factorization over the
centered product alias set from (2.45), and transports the already sealed
one-dimensional bound coordinatewise.

No alias-cardinality estimate appears: the factorization is the ring identity
`Finset.sum_prod_piFinset`.  This module does not yet prove that the complete
physical integrand is bounded by this product weight, nor the uniform analytic
strip following (2.51).

Source catalog key: `cmp89.local-green.fourier.2.34-2.51`.
-/

namespace YangMills.RG

noncomputable section

/-- The literal product of the coordinate weights used in the final line of
CMP89 (2.51). -/
def cmp89Eq251MultidimensionalAliasWeight
    {d : ℕ} (s : ℝ) (m : Fin d → ℤ) : ℝ :=
  ∏ mu, cmp89Eq251OneDimensionalAliasWeight s (m mu)

/-- The multidimensional product weight is nonnegative. -/
theorem cmp89Eq251MultidimensionalAliasWeight_nonneg
    {d : ℕ} (s : ℝ) (m : Fin d → ℤ) :
    0 ≤ cmp89Eq251MultidimensionalAliasWeight s m := by
  rw [cmp89Eq251MultidimensionalAliasWeight]
  exact Finset.prod_nonneg fun mu _ =>
    cmp89Eq251OneDimensionalAliasWeight_nonneg s (m mu)

/-- The finite centered `d`-dimensional product-weight sum. -/
def cmp89Eq251CenteredMultidimensionalAliasSum
    (d N : ℕ) (s : ℝ) : ℝ :=
  ∑ m ∈ cmp89Eq245CenteredAliasVectors d N,
    cmp89Eq251MultidimensionalAliasWeight s m

/-- Exact finite-product factorization of the centered alias sum.  This is the
algebraic last equality in CMP89 (2.51), before applying the one-dimensional
summability bound. -/
theorem cmp89Eq251CenteredMultidimensionalAliasSum_eq_pow
    (d N : ℕ) (s : ℝ) :
    cmp89Eq251CenteredMultidimensionalAliasSum d N s =
      cmp89Eq251CenteredOneDimensionalAliasSum N s ^ d := by
  simp only [cmp89Eq251CenteredMultidimensionalAliasSum,
    cmp89Eq245CenteredAliasVectors,
    cmp89Eq251MultidimensionalAliasWeight,
    cmp89Eq251CenteredOneDimensionalAliasSum]
  rw [Finset.sum_prod_piFinset]
  simp

/-- Uniform `d`-dimensional product bound obtained from the sealed coordinate
series. -/
theorem cmp89Eq251CenteredMultidimensionalAliasSum_le_tsum_pow
    (d N : ℕ) {s : ℝ} (hs : 1 < s) :
    cmp89Eq251CenteredMultidimensionalAliasSum d N s ≤
      (∑' m : ℤ, cmp89Eq251OneDimensionalAliasWeight s m) ^ d := by
  rw [cmp89Eq251CenteredMultidimensionalAliasSum_eq_pow]
  have hfiniteNonneg :
      0 ≤ cmp89Eq251CenteredOneDimensionalAliasSum N s := by
    rw [cmp89Eq251CenteredOneDimensionalAliasSum]
    exact Finset.sum_nonneg fun m _ =>
      cmp89Eq251OneDimensionalAliasWeight_nonneg s m
  exact pow_le_pow_left₀ hfiniteNonneg
    (cmp89Eq251CenteredOneDimensionalAliasSum_le_tsum N hs) d

/-- Source-parameter form of the uniform `d`-dimensional alias product bound
in the final line of CMP89 (2.51). -/
theorem cmp89Eq251CenteredMultidimensionalAliasSum_source_le_tsum_pow
    {d : ℕ} (N : ℕ) {alpha : ℝ} (hd : 0 < d) (halpha : alpha < 1) :
    cmp89Eq251CenteredMultidimensionalAliasSum d N
        (cmp89Eq251AliasSeriesExponent d alpha) ≤
      (∑' m : ℤ,
        cmp89Eq251OneDimensionalAliasWeight
          (cmp89Eq251AliasSeriesExponent d alpha) m) ^ d :=
  cmp89Eq251CenteredMultidimensionalAliasSum_le_tsum_pow d N
    (one_lt_cmp89Eq251AliasSeriesExponent hd halpha)

end

end YangMills.RG
