import YangMills.RG.BalabanCMP99SourceSeparatedSourceFlowFlatPhysicalGreenIdentification
import YangMills.RG.BalabanCMP99SourceFlatFullComplexPrecisionPointSourceInverseUniqueness
import YangMills.RG.BalabanCMP99SourceFlatQprimePhysicalCentralAveragePairNonvanishing

/-!
# PRE-VALIDATION: source-flow full Green on a fine point source

Source is present; the `.olean` is not materialized and this result is not
verified by the compiler. This source is not yet imported by the root aggregator.

F1 uses the already constructed source-flow left inverse of the literal
full-box precision. No generated coefficient is identified with a source
coefficient, no point-source equality is an input, and no Q'^* is applied.
The RG ratio L, localization size K and depth remain independent.
No owner/uniform/regional estimate or window-15 attainment is claimed.
-/

namespace YangMills.RG

open YangMills

noncomputable section

variable {L K Q Nc : ℕ}
variable [NeZero L] [NeZero K] [NeZero Q] [NeZero Nc]

/-- The internally solved full Eq. (2.46) point-source field is the actual
source-flow Green applied to that fine point source, by inverse uniqueness.
All nonvanishing premises are supplied internally at mass zero. -/
theorem cmp99SourceFlowFullPointSourceSolution_eq_green_apply
    (hL : 2 ≤ L) (depth : ℕ) {a : ℝ} (ha : 0 < a)
    (source : FinBox 4 (L ^ (depth + 1) * (2 * (K * Q))))
    (v : SUNLieComplexCoord Nc) :
    cmp99SourceFlatFullComplexPrecisionPointSourceSolution
        (d := 4) (M := L ^ (depth + 1)) (N' := 2 * (K * Q))
        (Nc := Nc) 0 (cmp99SourceFlowFlatFullComplexA a L depth)
        source v =
      cmp99SourceSeparatedSourceFlowFlatPhysicalStep7bGreenCLM
        (L := L) (K := K) (Q := Q) (Nc := Nc) hL depth ha
        (cmp99FlatComplexFibrePointSource source v) := by
  apply cmp99SourceFlatFullComplexPrecisionPointSourceSolution_eq_inverse_apply
    (d := 4) (M := L ^ (depth + 1)) (N' := 2 * (K * Q)) (Nc := Nc)
  · exact cmp99SourceSeparatedSourceFlowFlatPhysicalStep7bGreenCLM_comp_precision
      (L := L) (K := K) (Q := Q) (Nc := Nc) hL depth ha
  · intro ell k hk
    exact cmp99SourceFlatQprimePhysicalFineSymbol_massZero_ne_zero_noncentral
      ell k hk
  · exact cmp99SourceSeparatedSourceFlowFlatPhysicalStabilizedAliasDenominator_ne_zero
      L K Q depth ha
  · intro ell
    exact cmp89Eq249CentralEntireAveragePair_physicalCoarse_ne_zero ell

end

end YangMills.RG
