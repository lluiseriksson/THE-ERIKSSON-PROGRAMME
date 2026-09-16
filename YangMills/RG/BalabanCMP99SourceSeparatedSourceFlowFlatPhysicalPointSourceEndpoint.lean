/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99FlatComplexFibrePointSourceFourierReconstruction
import YangMills.RG.BalabanCMP99SourceSeparatedSourceFlowFlatPhysicalEndpointIntegrand

/-!
# Source-flow separated Green on one coarse point source

The exact point-source Fourier reconstruction and the fixed-target source-flow
C0 endpoint are composed here.  The result is a single normalized finite sum
of literal CMP89 endpoint-integrand values with `ell`, `x` and `y` kept in one
common scope.  This is the source-flow finite column to which residue-zero
aliasing will later be applied.

No generated coefficient, Fourier-series equality, coefficient bound, owner
transport, regional `B0`, window-15 attainment or terminal field is asserted
here.
-/

namespace YangMills.RG

open YangMills
open scoped BigOperators

noncomputable section

variable {L K Q Nc : ℕ}
variable [NeZero L] [NeZero K] [NeZero Q] [NeZero Nc]

/-- The internally constructed source-flow `G Q'^*` applied to one literal
coarse point source is exactly the normalized finite sum of the complete
CMP89 endpoint integrand, with no generated coefficient or target-dependent
readout supplied by the caller. -/
theorem
    cmp99SourceSeparatedSourceFlowFlatPhysicalGreenQprimeStar_pointSource_apply_eq_normalized_sum_endpointIntegrand
    (hL : 2 ≤ L) (depth : ℕ) {a : ℝ} (ha : 0 < a)
    (y : FinBox 4 (2 * (K * Q)))
    (v : SUNLieComplexCoord Nc)
    (x : FinBox 4 (L ^ (depth + 1) * (2 * (K * Q)))) :
    (((cmp99SourceSeparatedSourceFlowFlatPhysicalStep7bGreenCLM
          (L := L) (K := K) (Q := Q) (Nc := Nc) hL depth ha).comp
        (cmp99SourceFlatFullComplexWeightedAdjointCLM
          (d := 4) (M := L ^ (depth + 1))
          (N' := 2 * (K * Q)) (Nc := Nc)))
        (cmp99FlatComplexFibrePointSource y v)) x =
      ((((2 * (K * Q) : ℕ) : ℂ) ^ 4)⁻¹) •
        ∑ ell : FinBox 4 (2 * (K * Q)),
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
  let T :=
    (cmp99SourceSeparatedSourceFlowFlatPhysicalStep7bGreenCLM
      (L := L) (K := K) (Q := Q) (Nc := Nc) hL depth ha).comp
      (cmp99SourceFlatFullComplexWeightedAdjointCLM
        (d := 4) (M := L ^ (depth + 1))
        (N' := 2 * (K * Q)) (Nc := Nc))
  have hreconstruction :=
    ContinuousLinearMap_apply_cmp99FlatComplexFibrePointSource_eq
      T y v
  calc
    T (cmp99FlatComplexFibrePointSource y v) x =
        (((((2 * (K * Q) : ℕ) : ℂ) ^ 4)⁻¹) •
          ∑ ell : FinBox 4 (2 * (K * Q)),
            (cmp99FlatFourierMode ell y)⁻¹ •
              T (cmp99FlatComplexFibreFourierMode ell v)) x :=
      congrFun hreconstruction x
    _ = (((2 * (K * Q) : ℕ) : ℂ) ^ 4)⁻¹ •
        ∑ ell : FinBox 4 (2 * (K * Q)),
          (cmp99FlatFourierMode ell y)⁻¹ •
            T (cmp99FlatComplexFibreFourierMode ell v) x := by
      simp only [Pi.smul_apply, Finset.sum_apply]
    _ = _ := by
      apply congrArg (fun w =>
        ((((2 * (K * Q) : ℕ) : ℂ) ^ 4)⁻¹) • w)
      apply Finset.sum_congr rfl
      intro ell _
      exact
        cmp99SourceSeparatedSourceFlowFlatPhysicalGreenQprimeStar_fourierMode_coarseInv_apply_eq_endpointIntegrand_smul
          (L := L) (K := K) (Q := Q) (Nc := Nc)
          hL depth ha ell v x y

end

end YangMills.RG
