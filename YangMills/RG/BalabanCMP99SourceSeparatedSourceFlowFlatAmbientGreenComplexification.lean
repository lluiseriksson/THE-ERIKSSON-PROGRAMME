/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceSeparatedSourceFlowFlatAmbientGreen
import YangMills.RG.FinitePiLpCanonicalComplexificationOuterTransport

/-!
# Complexification of the source-flow separated flat ambient Green

This file canonically complexifies the literal source-flow inverse pair and
transports both inverse laws.  The coefficient remains
`cmp99SourceMassParameter a L depth`; no generated Poincare coefficient,
full-box dictionary, regional `B0` or window-15 attainment is asserted.
-/

namespace YangMills.RG

noncomputable section

variable {L K Q Nc : ℕ}
variable [NeZero L] [NeZero K] [NeZero Q] [NeZero Nc]

/-- Canonical complexification of the literal source-flow separated flat
ambient precision. -/
noncomputable def cmp99SourceSeparatedSourceFlowFlatAmbientPrecisionComplex
    (hL : 2 ≤ L) (depth : ℕ) (a : ℝ) :
    (FinBox 4
        (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)) →
      EuclideanSpace ℂ (Fin (Nc ^ 2 - 1))) →L[ℂ]
    (FinBox 4
        (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)) →
      EuclideanSpace ℂ (Fin (Nc ^ 2 - 1))) :=
  finitePiLpCanonicalComplexificationOuterCLM
    (cmp99SourceSeparatedSourceFlowFlatAmbientPrecision
      (L := L) (K := K) (Q := Q) (Nc := Nc) hL depth a)

/-- Canonical complexification of the Green constructed from the same literal
source-flow precision. -/
noncomputable def cmp99SourceSeparatedSourceFlowFlatAmbientGreenComplex
    (hL : 2 ≤ L) (depth : ℕ) {a : ℝ} (ha : 0 < a) :
    (FinBox 4
        (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)) →
      EuclideanSpace ℂ (Fin (Nc ^ 2 - 1))) →L[ℂ]
    (FinBox 4
        (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)) →
      EuclideanSpace ℂ (Fin (Nc ^ 2 - 1))) :=
  finitePiLpCanonicalComplexificationOuterCLM
    (cmp99SourceSeparatedSourceFlowFlatAmbientGreen
      (L := L) (K := K) (Q := Q) (Nc := Nc) hL depth ha)

/-- The complex source-flow precision followed by its internally constructed
complex Green is the identity. -/
theorem cmp99SourceSeparatedSourceFlowFlatAmbientPrecisionComplex_comp_green
    (hL : 2 ≤ L) (depth : ℕ) {a : ℝ} (ha : 0 < a) :
    (cmp99SourceSeparatedSourceFlowFlatAmbientPrecisionComplex
      (L := L) (K := K) (Q := Q) (Nc := Nc) hL depth a).comp
        (cmp99SourceSeparatedSourceFlowFlatAmbientGreenComplex
          (L := L) (K := K) (Q := Q) (Nc := Nc) hL depth ha) =
      ContinuousLinearMap.id ℂ
        (FinBox 4
          (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)) →
          EuclideanSpace ℂ (Fin (Nc ^ 2 - 1))) := by
  exact finitePiLpCanonicalComplexificationOuterCLM_comp_eq_id
    (cmp99SourceSeparatedSourceFlowFlatAmbientPrecision
      (L := L) (K := K) (Q := Q) (Nc := Nc) hL depth a)
    (cmp99SourceSeparatedSourceFlowFlatAmbientGreen
      (L := L) (K := K) (Q := Q) (Nc := Nc) hL depth ha)
    (cmp99SourceSeparatedSourceFlowFlatAmbientPrecision_comp_green
      (L := L) (K := K) (Q := Q) (Nc := Nc) hL depth ha)

/-- The internally constructed complex source-flow Green followed by the same
complex precision is the identity. -/
theorem cmp99SourceSeparatedSourceFlowFlatAmbientGreenComplex_comp_precision
    (hL : 2 ≤ L) (depth : ℕ) {a : ℝ} (ha : 0 < a) :
    (cmp99SourceSeparatedSourceFlowFlatAmbientGreenComplex
      (L := L) (K := K) (Q := Q) (Nc := Nc) hL depth ha).comp
        (cmp99SourceSeparatedSourceFlowFlatAmbientPrecisionComplex
          (L := L) (K := K) (Q := Q) (Nc := Nc) hL depth a) =
      ContinuousLinearMap.id ℂ
        (FinBox 4
          (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)) →
          EuclideanSpace ℂ (Fin (Nc ^ 2 - 1))) := by
  exact finitePiLpCanonicalComplexificationOuterCLM_comp_eq_id
    (cmp99SourceSeparatedSourceFlowFlatAmbientGreen
      (L := L) (K := K) (Q := Q) (Nc := Nc) hL depth ha)
    (cmp99SourceSeparatedSourceFlowFlatAmbientPrecision
      (L := L) (K := K) (Q := Q) (Nc := Nc) hL depth a)
    (cmp99SourceSeparatedSourceFlowFlatAmbientGreen_comp_precision
      (L := L) (K := K) (Q := Q) (Nc := Nc) hL depth ha)

end

end YangMills.RG
