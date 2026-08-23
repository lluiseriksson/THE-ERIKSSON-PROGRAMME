/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceSeparatedSourceFlowFlatPhysicalGreenIdentification
import YangMills.RG.BalabanCMP99SourceGeneratedFlatPhysicalGreenFourierSynthesis

/-!
# Source-flow separated flat physical Green Fourier endpoint

PRE-VALIDATION: source present; `.olean` not yet materialized and the result
has not yet been verified by the compiler.

This is the literal-source-flow counterpart of Step 8b.24/S4.  It specializes
the generic one-mode and inverse-DFT algebra to fine block side
`L^(depth+1)` and coarse side `2*(K*Q)`, after the source-flow physical Green
has been constructed internally and identified by inverse uniqueness.

The positive Fourier character and transposed stabilized alias coefficient
remain separate named factors.  No generated Poincare coefficient,
periodization, owner-distance bound, regional `B0`, window-15 attainment or
terminal field is asserted here.
-/

namespace YangMills.RG

open YangMills

noncomputable section

variable {L K Q Nc : ℕ}
variable [NeZero L] [NeZero K] [NeZero Q] [NeZero Nc]

/-- Source-flow separated endpoint on one coarse Fourier mode. -/
theorem cmp99SourceSeparatedSourceFlowFlatPhysicalGreenQprimeStar_fourierMode
    (hL : 2 ≤ L) (depth : ℕ) {a : ℝ} (ha : 0 < a)
    (ell : FinBox 4 (2 * (K * Q)))
    (v : SUNLieComplexCoord Nc) :
    ((cmp99SourceSeparatedSourceFlowFlatPhysicalStep7bGreenCLM
        (L := L) (K := K) (Q := Q) (Nc := Nc) hL depth ha).comp
      (cmp99SourceFlatFullComplexWeightedAdjointCLM
        (d := 4) (M := L ^ (depth + 1)) (N' := 2 * (K * Q))
          (Nc := Nc)))
        (cmp99FlatComplexFibreFourierMode ell v) =
      cmp99SourceFlatFullComplexPrecisionStabilizedParticularSolution
        (d := 4) (M := L ^ (depth + 1)) (N' := 2 * (K * Q))
        (Nc := Nc) ell 0 (cmp99SourceFlowFlatFullComplexA a L depth) v := by
  have hgate := congrArg
    (fun T :
        (FinBox 4 (2 * (K * Q)) → SUNLieComplexCoord Nc) →L[ℂ]
          (FinBox 4 (L ^ (depth + 1) * (2 * (K * Q))) →
            SUNLieComplexCoord Nc) =>
      T (cmp99FlatComplexFibreFourierMode ell v))
    (cmp99SourceSeparatedSourceFlowFlatPhysicalStabilizedFieldCLM_eq_green_comp
      (L := L) (K := K) (Q := Q) (Nc := Nc) hL depth ha)
  simpa only [
    cmp99SourceFlatFullComplexPrecisionStabilizedQprimeStarFieldCLM_apply,
    cmp99SourceFlatFullComplexPrecisionStabilizedQprimeStarField_fourierMode]
    using hgate.symm

/-- On the selected reciprocal fibre, the source-flow separated endpoint has
the literal stabilized alias coefficient and fine-volume factor. -/
theorem
    cmp99FlatPhysicalFibreDFT_sourceSeparatedSourceFlowFlatPhysicalGreenQprimeStar_fourierMode
    (hL : 2 ≤ L) (depth : ℕ) {a : ℝ} (ha : 0 < a)
    (ell : FinBox 4 (2 * (K * Q)))
    (v : SUNLieComplexCoord Nc)
    (k : CMP99SourceFlatQprimeFixedCoarseFibre
      4 (L ^ (depth + 1)) (2 * (K * Q)) ell) :
    cmp99FlatPhysicalFibreDFT
        (((cmp99SourceSeparatedSourceFlowFlatPhysicalStep7bGreenCLM
            (L := L) (K := K) (Q := Q) (Nc := Nc) hL depth ha).comp
          (cmp99SourceFlatFullComplexWeightedAdjointCLM
            (d := 4) (M := L ^ (depth + 1)) (N' := 2 * (K * Q))
              (Nc := Nc)))
          (cmp99FlatComplexFibreFourierMode ell v)) k.1 =
      ((((L ^ (depth + 1) * (2 * (K * Q)) : ℕ) : ℂ) ^ 4) *
          cmp99SourceFlatQprimePhysicalStabilizedAliasTransposeSolution
            ell 0 (cmp99SourceFlowFlatFullComplexA a L depth) k) • v := by
  rw [cmp99SourceSeparatedSourceFlowFlatPhysicalGreenQprimeStar_fourierMode
    (L := L) (K := K) (Q := Q) (Nc := Nc) hL depth ha ell v]
  exact cmp99FlatPhysicalFibreDFT_stabilizedParticularSolution_fixedCoarseFibre
    ell 0 (cmp99SourceFlowFlatFullComplexA a L depth) v k

/-- Outside the selected reciprocal fibre, the source-flow one-mode endpoint
has zero fine DFT. -/
theorem
    cmp99FlatPhysicalFibreDFT_sourceSeparatedSourceFlowFlatPhysicalGreenQprimeStar_fourierMode_eq_zero_of_coarseAlias_ne
    (hL : 2 ≤ L) (depth : ℕ) {a : ℝ} (ha : 0 < a)
    (ell : FinBox 4 (2 * (K * Q)))
    (v : SUNLieComplexCoord Nc)
    (k : FinBox 4 (L ^ (depth + 1) * (2 * (K * Q))))
    (hk : cmp99SourceFlatQprimeCoarseAlias k ≠ ell) :
    cmp99FlatPhysicalFibreDFT
        (((cmp99SourceSeparatedSourceFlowFlatPhysicalStep7bGreenCLM
            (L := L) (K := K) (Q := Q) (Nc := Nc) hL depth ha).comp
          (cmp99SourceFlatFullComplexWeightedAdjointCLM
            (d := 4) (M := L ^ (depth + 1)) (N' := 2 * (K * Q))
              (Nc := Nc)))
          (cmp99FlatComplexFibreFourierMode ell v)) k = 0 := by
  rw [cmp99SourceSeparatedSourceFlowFlatPhysicalGreenQprimeStar_fourierMode
    (L := L) (K := K) (Q := Q) (Nc := Nc) hL depth ha ell v]
  exact
    cmp99FlatPhysicalFibreDFT_stabilizedParticularSolution_eq_zero_of_coarseAlias_ne
      ell 0 (cmp99SourceFlowFlatFullComplexA a L depth) v k hk

/-- Source-flow Gate-7 endpoint in exact pointwise finite-synthesis form.  The
inverse-volume normalization cancels internally. -/
theorem
    cmp99SourceSeparatedSourceFlowFlatPhysicalGreenQprimeStar_fourierMode_apply_eq_sum_transposeGreenTerms
    (hL : 2 ≤ L) (depth : ℕ) {a : ℝ} (ha : 0 < a)
    (ell : FinBox 4 (2 * (K * Q)))
    (v : SUNLieComplexCoord Nc)
    (x : FinBox 4 (L ^ (depth + 1) * (2 * (K * Q)))) :
    (((cmp99SourceSeparatedSourceFlowFlatPhysicalStep7bGreenCLM
          (L := L) (K := K) (Q := Q) (Nc := Nc) hL depth ha).comp
        (cmp99SourceFlatFullComplexWeightedAdjointCLM
          (d := 4) (M := L ^ (depth + 1)) (N' := 2 * (K * Q))
            (Nc := Nc)))
        (cmp99FlatComplexFibreFourierMode ell v)) x =
      ∑ k : CMP99SourceFlatQprimeFixedCoarseFibre
          4 (L ^ (depth + 1)) (2 * (K * Q)) ell,
        cmp99SourceFlatPhysicalTransposeGreenFourierTerm
          ell 0 (cmp99SourceFlowFlatFullComplexA a L depth) x k • v := by
  rw [cmp99SourceSeparatedSourceFlowFlatPhysicalGreenQprimeStar_fourierMode
    (L := L) (K := K) (Q := Q) (Nc := Nc) hL depth ha ell v]
  exact
    cmp99SourceFlatFullComplexPrecisionStabilizedParticularSolution_apply_eq_sum_transposeGreenTerms
      ell 0 (cmp99SourceFlowFlatFullComplexA a L depth) v x

end

end YangMills.RG
