/-
PRE-VALIDATION -- source present; `.olean` not yet materialized and the
result is not yet compiler-verified.
-/

import YangMills.RG.BalabanCMP89SourceSeparatedAmbientPrefixPrecision
import YangMills.RG.BalabanCMP99SourceGeneratedFlatPhysicalGreen

/-!
# Source-flow flat ambient Green on the separated carrier

This file specializes the literal CMP85 positive-prefix precision and Green
to the flat background, zero source radius and canonical fine spacing.  The
coefficient remains the source flow `cmp99SourceMassParameter a L depth`;
the incompatible Poincare-generated full-complex coefficient does not occur.

Both inverse laws are inherited from the same internally constructed source
precision.  No complexification, Fourier/operator dictionary, regional
`B0`, window-15 attainment or terminal field is asserted here.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator RealInnerProductSpace

noncomputable section

variable {L K Q Nc : ℕ}
variable [NeZero L] [NeZero K] [NeZero Q] [NeZero Nc]

/-- The final positive prefix carries exactly the literal source-flow
coefficient at index `depth`. -/
theorem cmp85LastPositivePrefix_succ_sourceA_eq_massParameter
    (depth : ℕ) (a : ℝ) :
    cmp85SourcePrefixA (M := L) a
        (cmp85LastPositivePrefix (depth + 1) (Nat.succ_pos depth)) =
      cmp99SourceMassParameter a (L : ℝ) depth := by
  unfold cmp85SourcePrefixA
  rw [cmp85LastPositivePrefix_succ_sourceIndex]

/-- Literal source-flow precision at flat background, zero radius and
canonical fine spacing, transported to the separated ambient carrier. -/
noncomputable def cmp99SourceSeparatedSourceFlowFlatAmbientPrecision
    (hL : 2 ≤ L) (depth : ℕ) (a : ℝ) :
    GaugeZeroCochain 4
        (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q))
        (SUNLieCoord Nc) →L[ℝ]
      GaugeZeroCochain 4
        (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q))
        (SUNLieCoord Nc) :=
  cmp89SourceSeparatedAmbientPrefixPrecision
    (L := L) (K := K) (Q := Q) (Nc := Nc)
    hL depth
    (cmp99SourceGeneratedFullComplexSpacing L (depth + 1)) 0 a
    (cmp99SourceFlatGaugeConfig 4
      (cmp99RegionalLatticeSize L (2 * (K * Q)) (depth + 1)) Nc)
    (cmp99SourceFlatZeroClosedBudget
      (d := 4) (M := L) (Nc := Nc) (depth + 1))
    cmp99SourceFlatGaugeConfig_zero_small

/-- Green of the same literal source-flow precision.  Positivity, flat
small-field data and the zero Poincare-error budget are discharged inside. -/
noncomputable def cmp99SourceSeparatedSourceFlowFlatAmbientGreen
    (hL : 2 ≤ L) (depth : ℕ) {a : ℝ} (ha : 0 < a) :
    GaugeZeroCochain 4
        (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q))
        (SUNLieCoord Nc) →L[ℝ]
      GaugeZeroCochain 4
        (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q))
        (SUNLieCoord Nc) :=
  cmp89SourceSeparatedAmbientPrefixGreen
    (L := L) (K := K) (Q := Q) (Nc := Nc)
    hL depth
    (cmp99SourceGeneratedFullComplexSpacing_pos L (depth + 1)) ha
    (cmp99SourceFlatGaugeConfig 4
      (cmp99RegionalLatticeSize L (2 * (K * Q)) (depth + 1)) Nc)
    (cmp99SourceFlatZeroClosedBudget
      (d := 4) (M := L) (Nc := Nc) (depth + 1))
    cmp99SourceFlatGaugeConfig_zero_small
    (by simp)

/-- The flat source-flow precision followed by its internally constructed
Green is the identity. -/
theorem cmp99SourceSeparatedSourceFlowFlatAmbientPrecision_comp_green
    (hL : 2 ≤ L) (depth : ℕ) {a : ℝ} (ha : 0 < a) :
    (cmp99SourceSeparatedSourceFlowFlatAmbientPrecision
      (L := L) (K := K) (Q := Q) (Nc := Nc) hL depth a).comp
        (cmp99SourceSeparatedSourceFlowFlatAmbientGreen
          (L := L) (K := K) (Q := Q) (Nc := Nc) hL depth ha) =
      ContinuousLinearMap.id ℝ
        (GaugeZeroCochain 4
          (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q))
          (SUNLieCoord Nc)) := by
  exact cmp89SourceSeparatedAmbientPrefixPrecision_comp_green
    (L := L) (K := K) (Q := Q) (Nc := Nc)
    hL depth
    (cmp99SourceGeneratedFullComplexSpacing_pos L (depth + 1)) ha
    (cmp99SourceFlatGaugeConfig 4
      (cmp99RegionalLatticeSize L (2 * (K * Q)) (depth + 1)) Nc)
    (cmp99SourceFlatZeroClosedBudget
      (d := 4) (M := L) (Nc := Nc) (depth + 1))
    cmp99SourceFlatGaugeConfig_zero_small
    (by simp)

/-- The internally constructed flat source-flow Green followed by that same
precision is the identity. -/
theorem cmp99SourceSeparatedSourceFlowFlatAmbientGreen_comp_precision
    (hL : 2 ≤ L) (depth : ℕ) {a : ℝ} (ha : 0 < a) :
    (cmp99SourceSeparatedSourceFlowFlatAmbientGreen
      (L := L) (K := K) (Q := Q) (Nc := Nc) hL depth ha).comp
        (cmp99SourceSeparatedSourceFlowFlatAmbientPrecision
          (L := L) (K := K) (Q := Q) (Nc := Nc) hL depth a) =
      ContinuousLinearMap.id ℝ
        (GaugeZeroCochain 4
          (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q))
          (SUNLieCoord Nc)) := by
  exact cmp89SourceSeparatedAmbientPrefixGreen_comp_precision
    (L := L) (K := K) (Q := Q) (Nc := Nc)
    hL depth
    (cmp99SourceGeneratedFullComplexSpacing_pos L (depth + 1)) ha
    (cmp99SourceFlatGaugeConfig 4
      (cmp99RegionalLatticeSize L (2 * (K * Q)) (depth + 1)) Nc)
    (cmp99SourceFlatZeroClosedBudget
      (d := 4) (M := L) (Nc := Nc) (depth + 1))
    cmp99SourceFlatGaugeConfig_zero_small
    (by simp)

end

end YangMills.RG
