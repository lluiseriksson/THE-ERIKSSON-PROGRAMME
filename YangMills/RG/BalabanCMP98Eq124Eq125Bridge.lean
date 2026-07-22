/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP98Eq125OrderedDictionary
import YangMills.RG.BalabanCMP98FourContourRightTrivialization

/-!
# Source bridge between CMP98 equations (124) and (125)

The four-contour calculation names the physical middle source before any
coordinate conversion.  Equation (125) describes the same source as a
transported Lie-coordinate line sum.  This module proves their literal
pointwise equality and keeps the extra inverse block length visible.
-/

namespace YangMills.RG

open YangMills Matrix

noncomputable section

variable {d M N' Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero N'] [NeZero Nc]

/-- The named middle source term in the four-contour decomposition is
literally the matrix realization of the transported line sum printed in
CMP98 (125). -/
theorem cmp98Eq124MiddlePrefixRightVariation_eq_eq125TransportedLineSum
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N')
    (x : {x : FinBox d (M * N') // x ∈ blockOf M N' b.1}) :
    cmp98Eq124MiddlePrefixRightVariation U A b x.1 =
      cmp98LieCoordMatrix
        (cmp98Eq125TransportedLineSum (matrixSUNAdjointModel Nc)
          U A b.1 x b.2) := by
  rw [cmp98LieCoordMatrix_eq125TransportedLineSum_eq_rightVariation]
  unfold cmp98Eq124MiddlePrefixRightVariation cmp98UbarContourFactors
    cmp98UbarContourFactorVariations
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one,
    cmp98ContourMatrixCurve_zero_eq_wilsonLine,
    cmp98Gamma1PrefixHolonomy]

/-- **Normalized block bridge.**  The main operator of CMP98 (125) is one
additional inverse block length times the `M⁻ᵈ` average of the literal
middle source extracted from (124). -/
theorem cmp98LieCoordMatrix_eq125MainAverageValue_eq_inv_mul_middleAverage
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N') :
    cmp98LieCoordMatrix
        (cmp98Eq125MainAverageValue (matrixSUNAdjointModel Nc) U A b) =
      (M : ℝ)⁻¹ •
        (((M : ℝ) ^ d)⁻¹ •
          ∑ x ∈ blockOf M N' b.1,
            cmp98Eq124MiddlePrefixRightVariation U A b x) := by
  rw [cmp98LieCoordMatrix_eq125MainAverageValue_normalized]
  apply congrArg (((M : ℝ)⁻¹) • ·)
  apply congrArg ((((M : ℝ) ^ d)⁻¹) • ·)
  rw [Finset.sum_subtype (blockOf M N' b.1) (fun _ => Iff.rfl)
    (fun x => cmp98Eq124MiddlePrefixRightVariation U A b x)]
  apply Finset.sum_congr rfl
  intro x _hx
  symm
  rw [cmp98Eq124MiddlePrefixRightVariation_eq_eq125TransportedLineSum
    U A b x]
  exact cmp98LieCoordMatrix_eq125TransportedLineSum_eq_rightVariation
    U A b x

end

end YangMills.RG
