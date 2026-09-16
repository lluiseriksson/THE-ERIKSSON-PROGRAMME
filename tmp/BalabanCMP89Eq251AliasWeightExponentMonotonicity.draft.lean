/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP89Eq251AliasWeightRedistribution

/-!
# PRE-VALIDATION: monotonicity of the CMP89 alias source weight

This source is a static support draft for C6c.1/H2b.  Its `.olean` has not
been materialized and none of the declarations below has been
compiler-verified.

The complex-strip Holder quotient has a source branch with radial power
`||q||^(alpha-1)` and a vertical correction with radial power `||q||^(-1)`.
The second branch redistributes at `alpha = 0`.  This module proves that its
stronger product decay is pointwise dominated by the single source weight at
general `0 <= alpha`.  Thus H2b can keep one literal alias series without
absorbing a second summation or an alias-cardinality factor into its constant.

No Holder carrier, quotient estimate, alias sum, `B0`, window-15 producer or
terminal field is accepted or produced here.
-/

namespace YangMills.RG

noncomputable section

/-- The printed source exponent is antitone in the Holder exponent. -/
theorem cmp89Eq251AliasSeriesExponent_antitone_draft
    {d : ℕ} (hd : 0 < d) {alpha beta : ℝ} (hab : alpha ≤ beta) :
    cmp89Eq251AliasSeriesExponent d beta ≤
      cmp89Eq251AliasSeriesExponent d alpha := by
  rw [cmp89Eq251AliasSeriesExponent, cmp89Eq251AliasSeriesExponent]
  have hdReal : 0 < (d : ℝ) := by exact_mod_cast hd
  have hnum : 1 - beta ≤ 1 - alpha := sub_le_sub_left hab 1
  exact add_le_add_left (div_le_div_of_nonneg_right hnum hdReal.le) 1

/-- A one-dimensional reciprocal-alias weight is antitone in its positive
base exponent.  The proof exposes the inverse base in `(0,1]`. -/
theorem cmp89Eq251OneDimensionalAliasWeight_antitone_exponent_draft
    {s t : ℝ} (hst : s ≤ t) (m : ℤ) :
    cmp89Eq251OneDimensionalAliasWeight t m ≤
      cmp89Eq251OneDimensionalAliasWeight s m := by
  let base : ℝ := 1 + |2 * Real.pi * (m : ℝ)|
  have hbasePos : 0 < base := by dsimp [base]; positivity
  have hbaseOne : 1 ≤ base := by dsimp [base]; positivity
  have hinvPos : 0 < base⁻¹ := inv_pos.mpr hbasePos
  have hinvOne : base⁻¹ ≤ 1 := by
    rw [inv_le_one₀ hbasePos]
    exact hbaseOne
  rw [cmp89Eq251OneDimensionalAliasWeight,
    cmp89Eq251OneDimensionalAliasWeight]
  change 1 / base ^ t ≤ 1 / base ^ s
  rw [one_div, one_div, ← Real.inv_rpow hbasePos.le,
    ← Real.inv_rpow hbasePos.le]
  exact Real.rpow_le_rpow_of_exponent_ge hinvPos hinvOne hst

/-- The full product alias weight inherits exponent antitonicity without a
dimension or cardinality factor. -/
theorem cmp89Eq251MultidimensionalAliasWeight_antitone_exponent_draft
    {d : ℕ} {s t : ℝ} (hst : s ≤ t) (m : Fin d → ℤ) :
    cmp89Eq251MultidimensionalAliasWeight t m ≤
      cmp89Eq251MultidimensionalAliasWeight s m := by
  rw [cmp89Eq251MultidimensionalAliasWeight,
    cmp89Eq251MultidimensionalAliasWeight]
  exact Finset.prod_le_prod
    (fun mu _ => cmp89Eq251OneDimensionalAliasWeight_nonneg t (m mu))
    (fun mu _ =>
      cmp89Eq251OneDimensionalAliasWeight_antitone_exponent_draft hst (m mu))

/-- The `alpha = 0` correction weight is pointwise no larger than the single
general-`alpha` source weight used by CMP89 (2.51). -/
theorem cmp89Eq251AliasWeight_alpha_zero_le_alpha_draft
    {d : ℕ} (hd : 0 < d) {alpha : ℝ} (halpha0 : 0 ≤ alpha)
    (m : Fin d → ℤ) :
    cmp89Eq251MultidimensionalAliasWeight
        (cmp89Eq251AliasSeriesExponent d 0) m ≤
      cmp89Eq251MultidimensionalAliasWeight
        (cmp89Eq251AliasSeriesExponent d alpha) m := by
  exact cmp89Eq251MultidimensionalAliasWeight_antitone_exponent_draft
    (cmp89Eq251AliasSeriesExponent_antitone_draft hd halpha0) m

end

end YangMills.RG
