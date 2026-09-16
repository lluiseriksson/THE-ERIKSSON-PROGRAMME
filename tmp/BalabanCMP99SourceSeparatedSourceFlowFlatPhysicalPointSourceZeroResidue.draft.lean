import YangMills.RG.BalabanCMP99SourceSeparatedSourceFlowFlatPhysicalPointSourceEndpoint
import YangMills.RG.BalabanCMP99SourceSeparatedSourceFlowFlatPhysicalZeroResidueAliasing

namespace YangMills.RG

open YangMills
open scoped BigOperators

noncomputable section

variable {L K Q Nc : ℕ}
variable [NeZero L] [NeZero K] [NeZero Q] [NeZero Nc]

theorem
    cmp99SourceSeparatedSourceFlowFlatPhysicalGreenQprimeStar_pointSource_apply_eq_zeroResidue_smul_draft
    (hL : 2 ≤ L) (depth : ℕ) {a : ℝ} (ha : 0 < a)
    (y : FinBox 4 (2 * (K * Q)))
    (v : SUNLieComplexCoord Nc)
    (x : FinBox 4 (L ^ (depth + 1) * (2 * (K * Q))))
    {rho : ℝ}
    (hrho : 0 < rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hwindow : CMP89Eq249CentralStabilizedComplexWindow
      (cmp99SourceFlowFlatFullComplexA a L depth) rho) :
    (((cmp99SourceSeparatedSourceFlowFlatPhysicalStep7bGreenCLM
          (L := L) (K := K) (Q := Q) (Nc := Nc) hL depth ha).comp
        (cmp99SourceFlatFullComplexWeightedAdjointCLM
          (d := 4) (M := L ^ (depth + 1))
          (N' := 2 * (K * Q)) (Nc := Nc)))
        (cmp99FlatComplexFibrePointSource y v)) x =
      (∑' n : CMP99FlatIntegerResidueClass 4 (2 * (K * Q)) 0,
        cmp89Eq248CenteredGreenPhysicalFourierCoefficient
          (L ^ (depth + 1)) 1 0
          (cmp99SourceFlowFlatFullComplexA a L depth)
          (fun mu =>
            -cmp99SourceFlatQprimeFineToCoarseEndpointDisplacement
              (L ^ (depth + 1)) x y mu) n) • v := by
  rw [
    cmp99SourceSeparatedSourceFlowFlatPhysicalGreenQprimeStar_pointSource_apply_eq_normalized_sum_endpointIntegrand
      (L := L) (K := K) (Q := Q) (Nc := Nc) hL depth ha y v x]
  rw [← Finset.sum_smul, smul_smul]
  rw [
    cmp99SourceSeparatedSourceFlowFlatPhysical_normalized_sum_endpointIntegrand_eq_zeroResidue
      (L := L) (K := K) (Q := Q) depth ha hrho hamplitude hradius hwindow
      (fun mu =>
        -cmp99SourceFlatQprimeFineToCoarseEndpointDisplacement
          (L ^ (depth + 1)) x y mu)]

end

end YangMills.RG
