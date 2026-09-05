/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceSeparatedSourceFlowFlatPhysicalGreenFourierEndpoint
import YangMills.RG.BalabanCMP99SourceFlatQprimeCompleteEndpointIntegrand

/-!
# Source-flow separated endpoint as the literal CMP89 integrand

For one coarse Fourier source, the source-flow S4 endpoint is the complete
finite sum of transposed physical Green terms.  Dividing by the same coarse
character at one fixed source site turns that sum into the sealed row-oriented
endpoint samples; their complete-fibre sum is the literal CMP89 stabilized
endpoint integrand.

The target `ell`, fine target `x` and coarse source `y` remain fixed across the
whole equality.  No generated coefficient, target-dependent readout,
Fourier-series aliasing, owner estimate, regional `B0`, window-15 attainment
or terminal field is asserted here.
-/

namespace YangMills.RG

open YangMills

noncomputable section

variable {L K Q Nc : ℕ}
variable [NeZero L] [NeZero K] [NeZero Q] [NeZero Nc]

/-- One source-flow separated Fourier mode, normalized at a fixed coarse
source site, is exactly the literal CMP89 endpoint integrand acting on the
same Lie-coordinate vector. -/
theorem
    cmp99SourceSeparatedSourceFlowFlatPhysicalGreenQprimeStar_fourierMode_coarseInv_apply_eq_endpointIntegrand_smul
    (hL : 2 ≤ L) (depth : ℕ) {a : ℝ} (ha : 0 < a)
    (ell : FinBox 4 (2 * (K * Q)))
    (v : SUNLieComplexCoord Nc)
    (x : FinBox 4 (L ^ (depth + 1) * (2 * (K * Q))))
    (y : FinBox 4 (2 * (K * Q))) :
    (cmp99FlatFourierMode ell y)⁻¹ •
        ((((cmp99SourceSeparatedSourceFlowFlatPhysicalStep7bGreenCLM
              (L := L) (K := K) (Q := Q) (Nc := Nc) hL depth ha).comp
            (cmp99SourceFlatFullComplexWeightedAdjointCLM
              (d := 4) (M := L ^ (depth + 1))
              (N' := 2 * (K * Q)) (Nc := Nc)))
            (cmp99FlatComplexFibreFourierMode ell v)) x) =
      cmp89Eq248ComplexStabilizedGreenEndpointIntegrand
          4 (L ^ (depth + 1)) 1 0
          (cmp99SourceFlowFlatFullComplexA a L depth)
          (cmp99SourceFlatQprimeCoarseAmplitudeBaseMomentum
            (cmp99FinBoxFourierNeg ell))
          (cmp89Eq249PhysicalFineLatticeDisplacement
            (((L ^ (depth + 1) : ℕ) : ℝ)⁻¹)
            (fun mu =>
              -cmp99SourceFlatQprimeFineToCoarseEndpointDisplacement
                (L ^ (depth + 1)) x y mu)) • v := by
  have hA : 0 < cmp99SourceFlowFlatFullComplexA a L depth := by
    simpa [cmp99SourceFlowFlatFullComplexA] using
      (cmp99SourceMassParameter_pos ha
        (by exact_mod_cast (NeZero.pos L)) depth)
  rw [
    cmp99SourceSeparatedSourceFlowFlatPhysicalGreenQprimeStar_fourierMode_apply_eq_sum_transposeGreenTerms
      (L := L) (K := K) (Q := Q) (Nc := Nc) hL depth ha ell v x]
  rw [← Finset.sum_smul, smul_smul, mul_comm]
  rw [
    sum_cmp99SourceFlatPhysicalTransposeGreenFourierTerm_mul_coarseInv_eq_endpointSamples
      ell 0 (cmp99SourceFlowFlatFullComplexA a L depth) x y]
  rw [
    sum_cmp99SourceFlatPhysicalTransposeGreenEndpointSample_eq_endpointIntegrand
      hA ell x y]

end

end YangMills.RG
