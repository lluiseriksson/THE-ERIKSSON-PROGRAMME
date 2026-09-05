/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceSeparatedSignedCutoffLaplacian

/-!
# CMP96 (2.40): signed cutoff-Laplacian species

CMP96 printed p. 229 defines the middle term of `K(h)` with a minus sign,
`-(Delta h)(x) * lambda(x)`.  The positive-`D^*D` product rule already sealed
in the tree instead writes

`Delta(h phi) = h Delta(phi) - linkDerivative + cutoffLaplacian`.

Consequently the existing positive cutoff correction is the contribution of
`-K(h)` to the parametrix identity, whereas the literal middle species inside
`K(h)` itself is its negative.  This file makes that convention a theorem.

The coefficient is the sealed signed tensor second difference with the
`48 * secondDerivBound / cutoffScale^2` estimate.  The older first-difference
`O(cutoffScale^-1)` estimate is not used.
-/

namespace YangMills.RG

open YangMills
open scoped RealInnerProductSpace

noncomputable section

variable {L K Q Nc : ℕ}
variable [NeZero L] [NeZero K] [NeZero Q] [NeZero Nc]

/-- The literal middle species of `K(h)` in CMP96 (2.39)/(2.40).

The minus sign is part of the source formula, not a norm-estimate convention.
-/
noncomputable def cmp96Eq240SourceSeparatedSignedCutoffLaplacianKTerm
    (P : CMP95SourceSmoothPartitionProfile) (depth : ℕ)
    (cell : FinBox 4 Q)
    (phi : GaugeZeroCochain 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q))
      (SUNLieCoord Nc))
    (x : FinBox 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q))) :
    SUNLieCoord Nc :=
  -(cmp99SourceSeparatedSignedCutoffLaplacianCoefficient
      (L := L) (K := K) P depth cell x • phi x)

/-- Source-sign dictionary: the middle species inside `K(h)` is the negative
of the positive cutoff correction appearing in the `D^*D` product rule. -/
theorem cmp96Eq240SourceSeparatedSignedCutoffLaplacianKTerm_eq_neg_correction
    (P : CMP95SourceSmoothPartitionProfile) (depth : ℕ)
    (cell : FinBox 4 Q)
    (phi : GaugeZeroCochain 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q))
      (SUNLieCoord Nc))
    (x : FinBox 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q))) :
    cmp96Eq240SourceSeparatedSignedCutoffLaplacianKTerm
        (L := L) (K := K) P depth cell phi x =
      -cmp99CutoffLaplacianCorrection (Nc := Nc) 1
        (cmp99SourceSeparatedSignedLargeBlockCutoff
          P L K Q depth cell) phi x := by
  unfold cmp96Eq240SourceSeparatedSignedCutoffLaplacianKTerm
  rw [cmp99CutoffLaplacianCorrection_one_eq_sourceSeparatedSignedCoefficient]

/-- The literal signed species retains the inverse-square cutoff scale. -/
theorem norm_cmp96Eq240SourceSeparatedSignedCutoffLaplacianKTerm_le
    (P : CMP95SourceSmoothPartitionProfile) (depth : ℕ)
    (cell : FinBox 4 Q)
    (phi : GaugeZeroCochain 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q))
      (SUNLieCoord Nc))
    (x : FinBox 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q))) :
    ‖cmp96Eq240SourceSeparatedSignedCutoffLaplacianKTerm
        (L := L) (K := K) P depth cell phi x‖ ≤
      ((48 * P.secondDerivBound) /
          cmp99SourceSeparatedLargeBlockCutoffScale L K depth ^ 2) *
        ‖phi x‖ := by
  unfold cmp96Eq240SourceSeparatedSignedCutoffLaplacianKTerm
  rw [norm_neg, norm_smul]
  exact mul_le_mul_of_nonneg_right
    (norm_cmp99SourceSeparatedSignedCutoffLaplacianCoefficient_le
      (L := L) (K := K) P depth cell x)
    (norm_nonneg _)

/-- The scale convention is inherited without a new normalization: multiplying
by the square of the generated range leaves the explicit `12 / K^2` budget. -/
theorem cmp96Eq240SourceSeparatedSignedCutoffLaplacianBudget_mul_range_sq
    (P : CMP95SourceSmoothPartitionProfile)
    (L K depth : ℕ) [NeZero L] [NeZero K] :
    ((48 * P.secondDerivBound) /
        cmp99SourceSeparatedLargeBlockCutoffScale L K depth ^ 2) *
      (L ^ (depth + 1) : ℝ) ^ 2 =
        (12 * P.secondDerivBound) / (K : ℝ) ^ 2 := by
  exact cmp99SourceSeparatedSignedCutoffLaplacianBudget_mul_range_sq
    P L K depth

end

end YangMills.RG
