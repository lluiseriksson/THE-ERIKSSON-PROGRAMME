/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Pi.Bounds
import YangMills.RG.BalabanCMP89Eq250FullDenominatorLower

/-!
# PRE-VALIDATION: the one-dimensional source series in CMP89 (2.51)

The source is present, but this module's `.olean` has not yet been materialized
and its declarations have not yet been verified by the Lean compiler.

CMP89 (2.51) reduces the `d`-dimensional alias estimate to the `d`-th power of
the one-dimensional reciprocal-lattice series

`sum_(m in 2*pi*Z) (1 + |m|)^(-(1 + (1-alpha)/d))`.

This module constructs the literal `2*pi*Z` weight, proves that the printed
exponent is greater than one when `alpha < 1` and `d > 0`, establishes
summability on all of `Z`, and dominates every finite centered alias window by
the same infinite-series constant.  The proof separates the central alias and
dominates every noncentral term by the standard integer `p`-series.

This module does not yet prove the `d`-fold product factorization, the complete
integrand estimate (2.51), or the analytic-strip continuation following it.

Source catalog key: `cmp89.local-green.fourier.2.34-2.51`.
-/

namespace YangMills.RG

noncomputable section

/-- The exponent `1 + (1-alpha)/d` printed in the final line of CMP89 (2.51). -/
def cmp89Eq251AliasSeriesExponent (d : ℕ) (alpha : ℝ) : ℝ :=
  1 + (1 - alpha) / (d : ℝ)

/-- The printed exponent is strictly greater than one for positive dimension
and `alpha < 1`. -/
theorem one_lt_cmp89Eq251AliasSeriesExponent
    {d : ℕ} {alpha : ℝ} (hd : 0 < d) (halpha : alpha < 1) :
    1 < cmp89Eq251AliasSeriesExponent d alpha := by
  rw [cmp89Eq251AliasSeriesExponent]
  have hdReal : 0 < (d : ℝ) := by exact_mod_cast hd
  have hnum : 0 < 1 - alpha := sub_pos.mpr halpha
  linarith [div_pos hnum hdReal]

/-- One literal reciprocal-lattice weight from the one-dimensional source
series in CMP89 (2.51), with `l = 2*pi*m`. -/
def cmp89Eq251OneDimensionalAliasWeight (s : ℝ) (m : ℤ) : ℝ :=
  1 / (1 + |2 * Real.pi * (m : ℝ)|) ^ s

/-- Every one-dimensional alias weight is nonnegative. -/
theorem cmp89Eq251OneDimensionalAliasWeight_nonneg
    (s : ℝ) (m : ℤ) :
    0 ≤ cmp89Eq251OneDimensionalAliasWeight s m := by
  rw [cmp89Eq251OneDimensionalAliasWeight]
  positivity

/-- Away from the central alias, the literal source weight is dominated by the
standard integer `p`-series. -/
theorem cmp89Eq251OneDimensionalAliasWeight_le_abs_int_rpow
    {s : ℝ} (hs : 1 < s) {m : ℤ} (hm : m ≠ 0) :
    cmp89Eq251OneDimensionalAliasWeight s m ≤ |(m : ℝ)| ^ (-s) := by
  have hmReal : (m : ℝ) ≠ 0 := by exact_mod_cast hm
  have hmAbsPos : 0 < |(m : ℝ)| := abs_pos.mpr hmReal
  have hscale : |(m : ℝ)| ≤ |2 * Real.pi * (m : ℝ)| := by
    rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : 0 ≤ (2 : ℝ)),
      abs_of_pos Real.pi_pos]
    nlinarith [Real.pi_gt_three, abs_nonneg (m : ℝ)]
  have hbase : |(m : ℝ)| ≤ 1 + |2 * Real.pi * (m : ℝ)| :=
    hscale.trans (le_add_of_nonneg_left zero_le_one)
  have hsNonpos : -s ≤ 0 := by linarith
  rw [cmp89Eq251OneDimensionalAliasWeight, one_div,
    ← Real.rpow_neg (by positivity : 0 ≤ 1 + |2 * Real.pi * (m : ℝ)|) s]
  exact Real.rpow_le_rpow_of_nonpos hmAbsPos hbase hsNonpos

/-- The one-dimensional source series of CMP89 (2.51) is summable whenever
its exponent is greater than one. -/
theorem summable_cmp89Eq251OneDimensionalAliasWeight
    {s : ℝ} (hs : 1 < s) :
    Summable (cmp89Eq251OneDimensionalAliasWeight s) := by
  let central : ℤ → ℝ := fun m => if m = 0 then 1 else 0
  let majorant : ℤ → ℝ := fun m => central m + |(m : ℝ)| ^ (-s)
  have hcentral : Summable central := by
    exact (hasSum_ite_eq (0 : ℤ) (1 : ℝ)).summable
  have hmajorant : Summable majorant := by
    exact hcentral.add (Real.summable_abs_int_rpow hs)
  refine hmajorant.of_nonneg_of_le
    (fun m => cmp89Eq251OneDimensionalAliasWeight_nonneg s m) ?_
  intro m
  by_cases hm : m = 0
  · subst m
    simp only [cmp89Eq251OneDimensionalAliasWeight, majorant, central,
      Int.cast_zero, mul_zero, abs_zero, add_zero, one_div, Real.one_rpow,
      if_pos rfl]
    exact le_add_of_nonneg_right (Real.rpow_nonneg 0 (-s))
  · have htail := cmp89Eq251OneDimensionalAliasWeight_le_abs_int_rpow hs hm
    simpa [majorant, central, hm] using htail

/-- The finite centered one-dimensional alias sum at block count `N`. -/
def cmp89Eq251CenteredOneDimensionalAliasSum (N : ℕ) (s : ℝ) : ℝ :=
  ∑ m ∈ cmp89Eq245CenteredAliasIntegers N,
    cmp89Eq251OneDimensionalAliasWeight s m

/-- Every centered finite alias window is bounded by the same infinite source
series, uniformly in its cardinality. -/
theorem cmp89Eq251CenteredOneDimensionalAliasSum_le_tsum
    (N : ℕ) {s : ℝ} (hs : 1 < s) :
    cmp89Eq251CenteredOneDimensionalAliasSum N s ≤
      ∑' m : ℤ, cmp89Eq251OneDimensionalAliasWeight s m := by
  rw [cmp89Eq251CenteredOneDimensionalAliasSum]
  exact (summable_cmp89Eq251OneDimensionalAliasWeight hs).sum_le_tsum
    (cmp89Eq245CenteredAliasIntegers N)
    (fun m _ => cmp89Eq251OneDimensionalAliasWeight_nonneg s m)

/-- Source-parameter form of the uniform finite-window bound in (2.51). -/
theorem cmp89Eq251CenteredOneDimensionalAliasSum_source_le_tsum
    {d : ℕ} (N : ℕ) {alpha : ℝ} (hd : 0 < d) (halpha : alpha < 1) :
    cmp89Eq251CenteredOneDimensionalAliasSum N
        (cmp89Eq251AliasSeriesExponent d alpha) ≤
      ∑' m : ℤ,
        cmp89Eq251OneDimensionalAliasWeight
          (cmp89Eq251AliasSeriesExponent d alpha) m :=
  cmp89Eq251CenteredOneDimensionalAliasSum_le_tsum N
    (one_lt_cmp89Eq251AliasSeriesExponent hd halpha)

end

end YangMills.RG
