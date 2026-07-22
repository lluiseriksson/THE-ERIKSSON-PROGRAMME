/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP98UbarFourContourVariation

/-!
# Physical linearization of the literal CMP98 logarithmic average

The ambient derivative of the logarithmic block average was previously
expressed through an unexpanded derivative of each four-contour deviation.  This
module evaluates that derivative on a physical one-cochain and replaces it,
inside every summand, by the complete ordered four-contour variation.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped BigOperators Matrix.Norms.L2Operator

noncomputable section

variable {d M N' Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero N'] [NeZero Nc]

local instance cmp98PhysicalLinearizationMatrixL2NormOneClass :
    NormOneClass (Matrix (Fin Nc) (Fin Nc) ℂ) where
  norm_one := by
    rw [← Matrix.diagonal_one]
    rw [Matrix.l2_opNorm_diagonal]
    simp

/-- The complete physical first variation of the logarithmic block average.
The ordered Mercator derivative is evaluated on the explicit four-contour
variation at every fine point in the source block. -/
def cmp98UbarLogAveragePhysicalVariation
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N') : Matrix (Fin Nc) (Fin Nc) ℂ :=
  ((M : ℝ) ^ d)⁻¹ •
    ∑ x ∈ blockOf M N' b.1,
      (∑' n : ℕ,
        nearLogTermFDeriv
          (cmp98UbarAmbientDeviationMatrix U b x 0) n)
        (cmp98UbarDeviationFirstVariation U A b x 0)

/-- The Fréchet derivative of the literal logarithmic average, evaluated on
a physical one-cochain, is exactly the explicit ordered expression above. -/
theorem fderiv_cmp98UbarLogAverage_zero_apply_physical
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N')
    (hsmall : ∀ x ∈ blockOf M N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix U b x 0‖ < 1) :
    fderiv ℝ (cmp98UbarLogAverage U b) 0
        (physicalSuTangentToAmbient
          (physicalCochainToSuMatrixTangent A)) =
      cmp98UbarLogAveragePhysicalVariation U A b := by
  let V : PhysicalAmbientMatrixTangent d (M * N') Nc :=
    physicalSuTangentToAmbient (physicalCochainToSuMatrixTangent A)
  have hfd := (hasFDerivAt_cmp98UbarLogAverage U b 0 hsmall).fderiv
  change (fderiv ℝ (cmp98UbarLogAverage U b) 0) V =
    cmp98UbarLogAveragePhysicalVariation U A b
  calc
    _ = (((M : ℝ) ^ d)⁻¹ •
        ∑ x ∈ blockOf M N' b.1,
          ((∑' n : ℕ,
              nearLogTermFDeriv
                (cmp98UbarAmbientDeviationMatrix U b x 0) n).comp
            (fderiv ℝ
              (fun W => cmp98UbarAmbientDeviationMatrix U b x W) 0))) V :=
      congrArg (fun L : PhysicalAmbientMatrixTangent d (M * N') Nc →L[ℝ]
        Matrix (Fin Nc) (Fin Nc) ℂ => L V) hfd
    _ = cmp98UbarLogAveragePhysicalVariation U A b := by
      simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sum_apply,
        ContinuousLinearMap.comp_apply, cmp98UbarLogAveragePhysicalVariation]
      apply congrArg (((M : ℝ) ^ d)⁻¹ • ·)
      apply Finset.sum_congr rfl
      intro x hx
      have hinner :
        (fderiv ℝ (fun W => cmp98UbarAmbientDeviationMatrix U b x W) 0) V =
          cmp98UbarDeviationFirstVariation U A b x 0 := by
        simpa [V] using
          (fderiv_cmp98UbarAmbientDeviationMatrix_zero_apply_physical
            U A b x)
      exact congrArg
        (fun Y => (∑' n : ℕ,
          nearLogTermFDeriv
            (cmp98UbarAmbientDeviationMatrix U b x 0) n) Y) hinner

end

end YangMills.RG
