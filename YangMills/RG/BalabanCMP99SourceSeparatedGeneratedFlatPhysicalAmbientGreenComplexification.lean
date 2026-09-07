/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceSeparatedGeneratedFlatPhysicalAmbientGreen
import YangMills.RG.FinitePiLpCanonicalComplexificationOuterTransport

/-!
# Complexification of the source-separated generated flat ambient Green

This file is the complex half of Step 8b.24/S1.  It canonically complexifies
the source-separated real inverse pair and transports both inverse laws.
It introduces no full-box precision dictionary and no free inverse data.
-/

namespace YangMills.RG

noncomputable section

variable {L K Q Nc : ℕ}
variable [NeZero L] [NeZero K] [NeZero Q] [NeZero Nc]

/-- Canonical complexification of the separated flat ambient precision. -/
noncomputable def
    cmp99SourceSeparatedGeneratedFlatPhysicalAmbientPrecisionComplex
    (hL : 2 ≤ L) (depth : ℕ) :
    (FinBox 4
        (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)) →
      EuclideanSpace ℂ (Fin (Nc ^ 2 - 1))) →L[ℂ]
    (FinBox 4
        (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)) →
      EuclideanSpace ℂ (Fin (Nc ^ 2 - 1))) :=
  finitePiLpCanonicalComplexificationOuterCLM
    (cmp99SourceSeparatedGeneratedFlatPhysicalAmbientPrecision
      (L := L) (K := K) (Q := Q) (Nc := Nc) hL depth)

/-- Canonical complexification of the separated flat ambient Green. -/
noncomputable def cmp99SourceSeparatedGeneratedFlatPhysicalAmbientGreenComplex
    (hL : 2 ≤ L) (depth : ℕ) :
    (FinBox 4
        (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)) →
      EuclideanSpace ℂ (Fin (Nc ^ 2 - 1))) →L[ℂ]
    (FinBox 4
        (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)) →
      EuclideanSpace ℂ (Fin (Nc ^ 2 - 1))) :=
  finitePiLpCanonicalComplexificationOuterCLM
    (cmp99SourceSeparatedGeneratedFlatPhysicalAmbientGreen
      (L := L) (K := K) (Q := Q) (Nc := Nc) hL depth)

/-- The complex separated precision followed by the complex separated Green
is the identity. -/
theorem
    cmp99SourceSeparatedGeneratedFlatPhysicalAmbientPrecisionComplex_comp_green
    (hL : 2 ≤ L) (depth : ℕ) :
    (cmp99SourceSeparatedGeneratedFlatPhysicalAmbientPrecisionComplex
      (L := L) (K := K) (Q := Q) (Nc := Nc) hL depth).comp
        (cmp99SourceSeparatedGeneratedFlatPhysicalAmbientGreenComplex
          (L := L) (K := K) (Q := Q) (Nc := Nc) hL depth) =
      ContinuousLinearMap.id ℂ
        (FinBox 4
          (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)) →
          EuclideanSpace ℂ (Fin (Nc ^ 2 - 1))) := by
  exact finitePiLpCanonicalComplexificationOuterCLM_comp_eq_id
    (cmp99SourceSeparatedGeneratedFlatPhysicalAmbientPrecision
      (L := L) (K := K) (Q := Q) (Nc := Nc) hL depth)
    (cmp99SourceSeparatedGeneratedFlatPhysicalAmbientGreen
      (L := L) (K := K) (Q := Q) (Nc := Nc) hL depth)
    (cmp99SourceSeparatedGeneratedFlatPhysicalAmbientPrecision_comp_green
      (L := L) (K := K) (Q := Q) (Nc := Nc) hL depth)

/-- The complex separated Green followed by the same complex separated
precision is the identity. -/
theorem
    cmp99SourceSeparatedGeneratedFlatPhysicalAmbientGreenComplex_comp_precision
    (hL : 2 ≤ L) (depth : ℕ) :
    (cmp99SourceSeparatedGeneratedFlatPhysicalAmbientGreenComplex
      (L := L) (K := K) (Q := Q) (Nc := Nc) hL depth).comp
        (cmp99SourceSeparatedGeneratedFlatPhysicalAmbientPrecisionComplex
          (L := L) (K := K) (Q := Q) (Nc := Nc) hL depth) =
      ContinuousLinearMap.id ℂ
        (FinBox 4
          (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)) →
          EuclideanSpace ℂ (Fin (Nc ^ 2 - 1))) := by
  exact finitePiLpCanonicalComplexificationOuterCLM_comp_eq_id
    (cmp99SourceSeparatedGeneratedFlatPhysicalAmbientGreen
      (L := L) (K := K) (Q := Q) (Nc := Nc) hL depth)
    (cmp99SourceSeparatedGeneratedFlatPhysicalAmbientPrecision
      (L := L) (K := K) (Q := Q) (Nc := Nc) hL depth)
    (cmp99SourceSeparatedGeneratedFlatPhysicalAmbientGreen_comp_precision
      (L := L) (K := K) (Q := Q) (Nc := Nc) hL depth)

end

end YangMills.RG
