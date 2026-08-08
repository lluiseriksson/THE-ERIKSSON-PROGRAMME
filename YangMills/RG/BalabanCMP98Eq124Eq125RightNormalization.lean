/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP98Eq124RightCoordinateBridge

/-!
# The extra inverse block length in CMP98 (124)--(125)

The right-frame calculation extracted from (118)--(120) produces the
block average with weight `M⁻ᵈ`.  The physical averaging operator printed in
(124) and isolated in (125) carries one further inverse block length.  This
file keeps that normalization visible, splits the normalized four-line
formula into its main and correction parts, and identifies the main part
with the already constructed ordered-path operator of (125).
-/

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {d M N' Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero N'] [NeZero Nc]

local instance cmp98Eq124Eq125RightNormalizationMatrixL2NormOneClass :
    NormOneClass (Matrix (Fin Nc) (Fin Nc) ℂ) where
  norm_one := by
    rw [← Matrix.diagonal_one, Matrix.l2_opNorm_diagonal]
    simp

/-- The unnormalized middle block average extracted from the first line of
the right-frame four-source formula. -/
def cmp98Eq124RightRawMainLine
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N') : Matrix (Fin Nc) (Fin Nc) ℂ :=
  ((M : ℝ) ^ d)⁻¹ •
    ∑ x ∈ blockOf M N' b.1,
      cmp98Eq124MiddlePrefixRightVariation U A b x

/-- The physical main line of (124), with its additional `M⁻¹`. -/
def cmp98Eq124RightMainLine
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N') : Matrix (Fin Nc) (Fin Nc) ℂ :=
  (M : ℝ)⁻¹ • cmp98Eq124RightRawMainLine U A b

/-- The correction sector before applying the additional source factor
`M⁻¹`. -/
def cmp98Eq124RightRawCorrection
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N') : Matrix (Fin Nc) (Fin Nc) ℂ :=
  cmp98Eq124RightPrintedFourLinePhysicalVariation U A b -
    cmp98Eq124RightRawMainLine U A b

/-- The fully normalized four-line matrix of CMP98 (124). -/
def cmp98Eq124RightNormalizedFourLinePhysicalVariation
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N') : Matrix (Fin Nc) (Fin Nc) ℂ :=
  (M : ℝ)⁻¹ • cmp98Eq124RightPrintedFourLinePhysicalVariation U A b

/-- The source-normalized formula is exactly its (125) main line plus the
remaining three correction groups of (124). -/
theorem cmp98Eq124RightNormalizedFourLine_eq_main_add_correction
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N') :
    cmp98Eq124RightNormalizedFourLinePhysicalVariation U A b =
      cmp98Eq124RightMainLine U A b +
        (M : ℝ)⁻¹ • cmp98Eq124RightRawCorrection U A b := by
  unfold cmp98Eq124RightNormalizedFourLinePhysicalVariation
    cmp98Eq124RightMainLine cmp98Eq124RightRawCorrection
  ext i j
  simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply,
    Complex.real_smul]
  ring

/-- The normalized main line is literally the matrix representative of the
ordered averaging operator in CMP98 (125). -/
theorem cmp98Eq124RightMainLine_eq_eq125MainAverageValue
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N') :
    cmp98Eq124RightMainLine U A b =
      cmp98LieCoordMatrix
        (cmp98Eq125MainAverageValue (matrixSUNAdjointModel Nc) U A b) := by
  symm
  exact cmp98LieCoordMatrix_eq125MainAverageValue_eq_inv_mul_middleAverage
    U A b

/-- The same main-line identification in the printed Hermitian convention
of (121). -/
theorem cmp98Eq121ToPrinted_eq124RightMainLine_eq_eq125
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N') :
    cmp98Eq121ToPrintedMatrix (cmp98Eq124RightMainLine U A b) =
      cmp98Eq121PrintedLieCoordMatrix
        (cmp98Eq125MainAverageValue (matrixSUNAdjointModel Nc) U A b) := by
  rw [cmp98Eq124RightMainLine_eq_eq125MainAverageValue,
    cmp98Eq121PrintedLieCoordMatrix_eq_toPrinted]

/-- The source curve of (120), after the physical inverse-block-length
normalization, is exactly the normalized four-line matrix of (124). -/
theorem inv_smul_deriv_cmp98Eq120SourceCurve_zero_eq_normalizedFourLine
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N')
    (hthird : ∀ x ∈ blockOf M N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix U b x 0‖ ≤ 1 / 3) :
    (M : ℝ)⁻¹ • deriv (cmp98Eq120SourceCurve U A b) 0 =
      cmp98Eq124RightNormalizedFourLinePhysicalVariation U A b := by
  rw [deriv_cmp98Eq120SourceCurve_zero_eq_fourLine U A b hthird]
  rfl

/-- Fully normalized and printed `(118)--(125)` endpoint. -/
theorem cmp98Eq121ToPrinted_inv_smul_deriv_eq_eq125_add_correction
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N')
    (hthird : ∀ x ∈ blockOf M N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix U b x 0‖ ≤ 1 / 3) :
    cmp98Eq121ToPrintedMatrix
        ((M : ℝ)⁻¹ • deriv (cmp98Eq120SourceCurve U A b) 0) =
      cmp98Eq121PrintedLieCoordMatrix
          (cmp98Eq125MainAverageValue (matrixSUNAdjointModel Nc) U A b) +
        cmp98Eq121ToPrintedMatrix
          ((M : ℝ)⁻¹ • cmp98Eq124RightRawCorrection U A b) := by
  rw [inv_smul_deriv_cmp98Eq120SourceCurve_zero_eq_normalizedFourLine
      U A b hthird,
    cmp98Eq124RightNormalizedFourLine_eq_main_add_correction]
  unfold cmp98Eq121ToPrintedMatrix
  have hdist :
      (Complex.I : ℂ)⁻¹ •
          (cmp98Eq124RightMainLine U A b +
            (M : ℝ)⁻¹ • cmp98Eq124RightRawCorrection U A b) =
        (Complex.I : ℂ)⁻¹ • cmp98Eq124RightMainLine U A b +
          (Complex.I : ℂ)⁻¹ •
            ((M : ℝ)⁻¹ • cmp98Eq124RightRawCorrection U A b) := by
    ext i j
    simp [mul_add]
  rw [hdist]
  exact congrArg
    (fun z => z + (Complex.I : ℂ)⁻¹ •
      ((M : ℝ)⁻¹ • cmp98Eq124RightRawCorrection U A b))
    (cmp98Eq121ToPrinted_eq124RightMainLine_eq_eq125 U A b)

end

end YangMills.RG
