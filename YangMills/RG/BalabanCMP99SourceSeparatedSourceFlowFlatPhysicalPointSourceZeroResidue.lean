/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceSeparatedSourceFlowFlatPhysicalPointSourceEndpoint
import YangMills.RG.BalabanCMP99SourceSeparatedSourceFlowFlatPhysicalZeroResidueAliasing

/-!
# Source-flow point-source Green as the zero-residue physical series

PRE-VALIDATION: source present; `.olean` not yet materialized and the result
has not yet been verified by the compiler.

C1b identifies the source-flow `G Q'^*` point-source column with the normalized
finite endpoint-integrand sum.  C2 identifies that scalar sum with the literal
zero-residue physical Green series.  This module composes those two exact
equalities and transports the scalar identity through the fixed
Lie-coordinate vector.

No generated coefficient, Fourier family, readout equality, Green inverse,
owner estimate, regional `B0`, window-15 attainment or terminal field is
supplied by the caller.
-/

namespace YangMills.RG

open YangMills
open scoped BigOperators

noncomputable section

variable {L K Q Nc : ℕ}
variable [NeZero L] [NeZero K] [NeZero Q] [NeZero Nc]

/-- The internally constructed source-flow `G Q'^*` applied to a literal
coarse point source is the zero-residue sum of physical fine Green
coefficients, acting on the same Lie-coordinate vector. -/
theorem
    cmp99SourceSeparatedSourceFlowFlatPhysicalGreenQprimeStar_pointSource_apply_eq_zeroResidue_smul
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
