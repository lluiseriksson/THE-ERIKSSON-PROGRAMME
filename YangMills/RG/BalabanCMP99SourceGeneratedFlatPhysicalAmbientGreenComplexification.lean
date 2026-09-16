/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceGeneratedFlatPhysicalAmbientGreen
import YangMills.RG.FinitePiLpCanonicalComplexificationOuterTransport

/-!
# Canonical complexification of the generated flat ambient Green

The generated flat ambient precision and Green are a two-sided inverse pair
on the real counting-Hilbert carrier.  This file applies the single canonical
finite-dimensional complexification to both operators and transports both
inverse laws to the ordinary finite complex function space.

No equality with the source full-box complex precision, Step-7b physical
dictionary, regional compression, or terminal contraction is asserted here.
-/

namespace YangMills.RG

noncomputable section

variable {M Q Nc : ℕ}
variable [NeZero M] [NeZero Q] [NeZero Nc]

/-- Canonical complexification of the generated flat ambient precision on the
ordinary finite complex function space. -/
noncomputable def cmp99SourceGeneratedFlatPhysicalAmbientPrecisionComplex
    (hM : 2 ≤ M) (depth : ℕ) :
    (FinBox 4 (cmp99SourceRegionalLargeBlockSide M depth * (2 * Q)) →
        EuclideanSpace ℂ (Fin (Nc ^ 2 - 1))) →L[ℂ]
      (FinBox 4 (cmp99SourceRegionalLargeBlockSide M depth * (2 * Q)) →
        EuclideanSpace ℂ (Fin (Nc ^ 2 - 1))) :=
  finitePiLpCanonicalComplexificationOuterCLM
    (cmp99SourceGeneratedFlatPhysicalAmbientPrecision
      (M := M) (Q := Q) (Nc := Nc) hM depth)

/-- Canonical complexification of the generated flat ambient Green on the
same ordinary finite complex function space. -/
noncomputable def cmp99SourceGeneratedFlatPhysicalAmbientGreenComplex
    (hM : 2 ≤ M) (depth : ℕ) :
    (FinBox 4 (cmp99SourceRegionalLargeBlockSide M depth * (2 * Q)) →
        EuclideanSpace ℂ (Fin (Nc ^ 2 - 1))) →L[ℂ]
      (FinBox 4 (cmp99SourceRegionalLargeBlockSide M depth * (2 * Q)) →
        EuclideanSpace ℂ (Fin (Nc ^ 2 - 1))) :=
  finitePiLpCanonicalComplexificationOuterCLM
    (cmp99SourceGeneratedFlatPhysicalAmbientGreen
      (M := M) (Q := Q) (Nc := Nc) hM depth)

/-- The complex ambient precision followed by the complex ambient Green is
the identity. -/
theorem cmp99SourceGeneratedFlatPhysicalAmbientPrecisionComplex_comp_green
    (hM : 2 ≤ M) (depth : ℕ) :
    (cmp99SourceGeneratedFlatPhysicalAmbientPrecisionComplex
      (M := M) (Q := Q) (Nc := Nc) hM depth).comp
        (cmp99SourceGeneratedFlatPhysicalAmbientGreenComplex
          (M := M) (Q := Q) (Nc := Nc) hM depth) =
      ContinuousLinearMap.id ℂ
        (FinBox 4 (cmp99SourceRegionalLargeBlockSide M depth * (2 * Q)) →
          EuclideanSpace ℂ (Fin (Nc ^ 2 - 1))) := by
  exact finitePiLpCanonicalComplexificationOuterCLM_comp_eq_id
    (cmp99SourceGeneratedFlatPhysicalAmbientPrecision
      (M := M) (Q := Q) (Nc := Nc) hM depth)
    (cmp99SourceGeneratedFlatPhysicalAmbientGreen
      (M := M) (Q := Q) (Nc := Nc) hM depth)
    (cmp99SourceGeneratedFlatPhysicalAmbientPrecision_comp_green
      (M := M) (Q := Q) (Nc := Nc) hM depth)

/-- The complex ambient Green followed by the same complex ambient precision
is the identity. -/
theorem cmp99SourceGeneratedFlatPhysicalAmbientGreenComplex_comp_precision
    (hM : 2 ≤ M) (depth : ℕ) :
    (cmp99SourceGeneratedFlatPhysicalAmbientGreenComplex
      (M := M) (Q := Q) (Nc := Nc) hM depth).comp
        (cmp99SourceGeneratedFlatPhysicalAmbientPrecisionComplex
          (M := M) (Q := Q) (Nc := Nc) hM depth) =
      ContinuousLinearMap.id ℂ
        (FinBox 4 (cmp99SourceRegionalLargeBlockSide M depth * (2 * Q)) →
          EuclideanSpace ℂ (Fin (Nc ^ 2 - 1))) := by
  exact finitePiLpCanonicalComplexificationOuterCLM_comp_eq_id
    (cmp99SourceGeneratedFlatPhysicalAmbientGreen
      (M := M) (Q := Q) (Nc := Nc) hM depth)
    (cmp99SourceGeneratedFlatPhysicalAmbientPrecision
      (M := M) (Q := Q) (Nc := Nc) hM depth)
    (cmp99SourceGeneratedFlatPhysicalAmbientGreen_comp_precision
      (M := M) (Q := Q) (Nc := Nc) hM depth)

end

end YangMills.RG
