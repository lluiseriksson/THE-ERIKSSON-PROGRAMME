/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceGaugePrecision
import YangMills.RG.BalabanCMP99SourceRegionalGreenNeumann

/-!
# Exact regional commutator split for the CMP99 source precision

PRE-VALIDATION: this source is present, but its `.olean` has not yet been
materialized and its result is not compiler-verified.

The source precision is the literal sum

`Delta'_a = Delta_U + a Q'^* Q'`.

This file splits its square commutator before any estimate is made.  The
covariant-Laplacian and normalized averaging-mass summands remain separately
recoverable; no common row constant is introduced.  This is only the ambient
operator algebra behind CMP99 (3.88).  It does not yet expand the two
Laplacian species or the normalized `Q'^* Q'` species printed there, and it
does not prove contraction of the regional Green defect.
-/

namespace YangMills.RG

open scoped RealInnerProductSpace

noncomputable section

variable {M Q : ℕ} [NeZero M] [NeZero Q]
variable {g F : Type*}
variable [NormedAddCommGroup g] [InnerProductSpace ℝ g]
  [FiniteDimensional ℝ g]
variable [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/-- Exact ambient split of the square commutator with
`Delta'_a = Delta_U + a Q'^* Q'`. -/
theorem cmp99RegionalSquareSourceGaugePrecisionCommutator_eq
    (P : CMP99RegionalFineSquarePartition M Q) (cell : FinBox 4 Q)
    (covariantLaplacian :
      GaugeZeroCochain 4 (M * (2 * Q)) g →L[ℝ]
        GaugeZeroCochain 4 (M * (2 * Q)) g)
    (Qprime : GaugeZeroCochain 4 (M * (2 * Q)) g →L[ℝ] F)
    (a : ℝ) :
    cmp99RegionalSquarePrecisionCommutator P cell
        (cmp99SourceGaugePrecision covariantLaplacian Qprime a) =
      cmp99RegionalSquarePrecisionCommutator P cell covariantLaplacian +
        a • cmp99RegionalSquarePrecisionCommutator P cell
          (Qprime.adjoint.comp Qprime) := by
  apply ContinuousLinearMap.ext
  intro phi
  simp only [cmp99RegionalSquarePrecisionCommutator,
    cmp99SourceGaugePrecision, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, map_add, map_smul]
  module

end

end YangMills.RG
