/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP89Eq249ComplexHolderRadialRedistribution
import YangMills.RG.BalabanCMP89Eq251MultidimensionalAliasProduct

/-!
# PRE-VALIDATION: general-alpha complex Holder alias summation

This H2c source is a static draft. Its `.olean` has not been materialized and
none of its declarations has been compiler-verified.

It sums exactly the single product weight produced by H2b. The finite centered
alias family is dominated by the already sealed one-dimensional `tsum` raised
to the fourth power. No factor depending on `L^j`, the number of aliases or a
second hidden series is introduced.

This module does not yet bound a literal complete complex integrand: H3/H4
must retain the endpoint transport exponential until its signed contour is
constructed. It does not construct `B0`, attain window 15, discharge a
terminal field or inhabit a `TermSource`.
-/

namespace YangMills.RG

noncomputable section

/-- Uniform H2c constant after the finite four-dimensional alias family is
dominated by the literal product `tsum`. -/
def cmp89Eq249ComplexHolderNoncentralAliasSumBound_draft
    (rho alpha : ℝ) : ℝ :=
  cmp89Eq249ComplexHolderNoncentralRadialConstant_draft rho alpha *
    (∑' n : ℤ,
      cmp89Eq251OneDimensionalAliasWeight
        (cmp89Eq251AliasSeriesExponent 4 alpha) n) ^ 4

/-- The H2b radial majorant is uniformly summable over every centered finite
alias family. Strict `alpha < 1` is the source summability threshold. -/
theorem cmp89Eq249_complexHolderCenteredAliasSum_le_uniform_draft
    (N : ℕ) {rho alpha : ℝ} (hrho : 0 ≤ rho) (halpha : alpha < 1) :
    cmp89Eq249ComplexHolderNoncentralRadialConstant_draft rho alpha *
        cmp89Eq251CenteredMultidimensionalAliasSum 4 N
          (cmp89Eq251AliasSeriesExponent 4 alpha) ≤
      cmp89Eq249ComplexHolderNoncentralAliasSumBound_draft rho alpha := by
  have hseries :=
    cmp89Eq251CenteredMultidimensionalAliasSum_source_le_tsum_pow
      (d := 4) N (by norm_num) halpha
  have hconstant :
      0 ≤ cmp89Eq249ComplexHolderNoncentralRadialConstant_draft rho alpha := by
    rw [cmp89Eq249ComplexHolderNoncentralRadialConstant_draft,
      cmp89Eq251ComplexNoncentralEndpointRadialConstant,
      cmp89Eq245EntireAverageAliasStripConstant]
    positivity
  rw [cmp89Eq249ComplexHolderNoncentralAliasSumBound_draft]
  exact mul_le_mul_of_nonneg_left hseries hconstant

end

end YangMills.RG
