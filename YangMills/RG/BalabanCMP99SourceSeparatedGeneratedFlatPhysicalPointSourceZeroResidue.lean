/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceSeparatedGeneratedFlatPhysicalPointSourceEndpoint
import YangMills.RG.BalabanCMP99SourceSeparatedGeneratedFlatPhysicalZeroResidueAliasing

/-!
# Generated point-source Green as the zero-residue physical series

PRE-VALIDATION: source present, `.olean` not yet materialized, and results in
this module are not yet compiler-verified.

C1b identifies the generated `G Q'^*` point-source column with a normalized
finite endpoint-integrand sum.  C2 identifies the scalar coefficient of that
same sum with the literal zero-residue physical Green series.  This module
composes those two exact equalities and transports the scalar identity through
the fixed Lie-coordinate vector.

No Fourier family, readout equality, Green inverse, owner estimate, regional
`B0`, window-15 attainment or terminal field is supplied by the caller.
-/

namespace YangMills.RG

open YangMills
open scoped BigOperators

noncomputable section

variable {L K Q Nc : ℕ}
variable [NeZero L] [NeZero K] [NeZero Q] [NeZero Nc]

/-- The internally generated source-separated `G Q'^*` applied to a literal
coarse point source is the zero-residue sum of the physical fine Green
coefficients, acting on the same Lie-coordinate vector.  The displacement is
the literal negative fine-to-coarse endpoint displacement from C0/C1b. -/
theorem
    cmp99SourceSeparatedGeneratedFlatPhysicalGreenQprimeStar_pointSource_apply_eq_zeroResidue_smul
    (hL : 2 ≤ L) (depth : ℕ)
    (y : FinBox 4 (2 * (K * Q)))
    (v : SUNLieComplexCoord Nc)
    (x : FinBox 4 (L ^ (depth + 1) * (2 * (K * Q))))
    {rho : ℝ}
    (hrho : 0 < rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hwindow : CMP89Eq249CentralStabilizedComplexWindow
      (cmp99SourceGeneratedFullComplexA 4 L (depth + 1)
        (cmp99SourceGeneratedFullComplexSpacing L (depth + 1)) 0) rho) :
    (((cmp99SourceSeparatedGeneratedFlatPhysicalStep7bGreenCLM
          (L := L) (K := K) (Q := Q) (Nc := Nc) hL depth).comp
        (cmp99SourceFlatFullComplexWeightedAdjointCLM
          (d := 4) (M := L ^ (depth + 1))
          (N' := 2 * (K * Q)) (Nc := Nc)))
        (cmp99FlatComplexFibrePointSource y v)) x =
      (∑' n : CMP99FlatIntegerResidueClass 4 (2 * (K * Q)) 0,
        cmp89Eq248CenteredGreenPhysicalFourierCoefficient
          (L ^ (depth + 1)) 1 0
          (cmp99SourceGeneratedFullComplexA 4 L (depth + 1)
            (cmp99SourceGeneratedFullComplexSpacing L (depth + 1)) 0)
          (fun mu =>
            -cmp99SourceFlatQprimeFineToCoarseEndpointDisplacement
              (L ^ (depth + 1)) x y mu) n) • v := by
  rw [
    cmp99SourceSeparatedGeneratedFlatPhysicalGreenQprimeStar_pointSource_apply_eq_normalized_sum_endpointIntegrand
      (L := L) (K := K) (Q := Q) (Nc := Nc) hL depth y v x]
  rw [← Finset.sum_smul, smul_smul]
  rw [
    cmp99SourceSeparatedGeneratedFlatPhysical_normalized_sum_endpointIntegrand_eq_zeroResidue
      (L := L) (K := K) (Q := Q) depth hrho hamplitude hradius hwindow
      (fun mu =>
        -cmp99SourceFlatQprimeFineToCoarseEndpointDisplacement
          (L ^ (depth + 1)) x y mu)]

end

end YangMills.RG
