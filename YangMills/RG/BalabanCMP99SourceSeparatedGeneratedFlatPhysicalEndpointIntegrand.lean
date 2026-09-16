/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceSeparatedGeneratedFlatPhysicalGreenFourierEndpoint
import YangMills.RG.BalabanCMP99SourceFlatQprimeCompleteEndpointIntegrand

/-!
# Source-separated generated endpoint as the literal CMP89 integrand

For one coarse Fourier source, S4 gives the generated `G Q'^*` output as the
complete finite sum of transposed physical Green terms.  Dividing by the
same coarse character at one fixed source site turns that complete sum into
the already sealed row-oriented endpoint samples; the complete-fibre
orientation bridge then identifies their sum with the literal CMP89
stabilized endpoint integrand.

The target `ell`, fine target `x` and coarse source `y` remain fixed across
the whole equality.  No sum over target-dependent readouts, Fourier-series
aliasing, owner estimate, regional `B0`, window-15 attainment or terminal
field is asserted here.
-/

namespace YangMills.RG

open YangMills

noncomputable section

variable {L K Q Nc : ℕ}
variable [NeZero L] [NeZero K] [NeZero Q] [NeZero Nc]

/-- One source-separated generated Fourier mode, normalized at a fixed
coarse source site, is exactly the literal CMP89 endpoint integrand acting
on the same Lie-coordinate vector.  All inverse, orientation and
nonvanishing data are inherited from the constructed S4 endpoint. -/
theorem
    cmp99SourceSeparatedGeneratedFlatPhysicalGreenQprimeStar_fourierMode_coarseInv_apply_eq_endpointIntegrand_smul
    (hL : 2 ≤ L) (depth : ℕ)
    (ell : FinBox 4 (2 * (K * Q)))
    (v : SUNLieComplexCoord Nc)
    (x : FinBox 4 (L ^ (depth + 1) * (2 * (K * Q))))
    (y : FinBox 4 (2 * (K * Q))) :
    (cmp99FlatFourierMode ell y)⁻¹ •
        ((((cmp99SourceSeparatedGeneratedFlatPhysicalStep7bGreenCLM
              (L := L) (K := K) (Q := Q) (Nc := Nc) hL depth).comp
            (cmp99SourceFlatFullComplexWeightedAdjointCLM
              (d := 4) (M := L ^ (depth + 1))
              (N' := 2 * (K * Q)) (Nc := Nc)))
            (cmp99FlatComplexFibreFourierMode ell v)) x) =
      cmp89Eq248ComplexStabilizedGreenEndpointIntegrand
          4 (L ^ (depth + 1)) 1 0
          (cmp99SourceGeneratedFullComplexA 4 L (depth + 1)
            (cmp99SourceGeneratedFullComplexSpacing L (depth + 1)) 0)
          (cmp99SourceFlatQprimeCoarseAmplitudeBaseMomentum
            (cmp99FinBoxFourierNeg ell))
          (cmp89Eq249PhysicalFineLatticeDisplacement
            (((L ^ (depth + 1) : ℕ) : ℝ)⁻¹)
            (fun mu =>
              -cmp99SourceFlatQprimeFineToCoarseEndpointDisplacement
                (L ^ (depth + 1)) x y mu)) • v := by
  rw [
    cmp99SourceSeparatedGeneratedFlatPhysicalGreenQprimeStar_fourierMode_apply_eq_sum_transposeGreenTerms
      (L := L) (K := K) (Q := Q) (Nc := Nc) hL depth ell v x]
  rw [← Finset.sum_smul, smul_smul, mul_comm]
  rw [
    sum_cmp99SourceFlatPhysicalTransposeGreenFourierTerm_mul_coarseInv_eq_endpointSamples
      ell 0
        (cmp99SourceGeneratedFullComplexA 4 L (depth + 1)
          (cmp99SourceGeneratedFullComplexSpacing L (depth + 1)) 0)
        x y]
  rw [
    sum_cmp99SourceFlatPhysicalTransposeGreenEndpointSample_eq_endpointIntegrand
      (cmp99SourceGeneratedFullComplexA_pos_physical L depth) ell x y]

end

end YangMills.RG
