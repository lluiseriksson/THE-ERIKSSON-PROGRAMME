/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP98Eq124RightPrintedBridge

/-!
# The CMP98 (121) coordinate convention for the right-frame (124) formula

Balaban's printed variable is Hermitian and carries a visible `1/i`, whereas
the repository differentiates matrix exponentials in skew-Hermitian
coordinates.  This file records the exact two-way coordinate conversion and
uses it to transport the source-selected right derivative

`g(ad (-Yrepo))`

to the printed `g(-i ad y)` convention, where `Yrepo = i y`.  The sign is
therefore derived from the source curve and the coordinate conversion; it is
not identified with the older left-trivialized `g(ad Yrepo)` formula.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {d M N' Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero N'] [NeZero Nc]

local instance cmp98Eq124RightCoordinateBridgeMatrixL2NormOneClass :
    NormOneClass (Matrix (Fin Nc) (Fin Nc) ℂ) where
  norm_one := by
    rw [← Matrix.diagonal_one, Matrix.l2_opNorm_diagonal]
    simp

/-- The visible `1/i` conversion from repository matrix coordinates to the
Hermitian coordinates printed in CMP98 (121). -/
def cmp98Eq121ToPrintedMatrix
    (H : Matrix (Fin Nc) (Fin Nc) ℂ) : Matrix (Fin Nc) (Fin Nc) ℂ :=
  (Complex.I : ℂ)⁻¹ • H

/-- The inverse conversion from the printed Hermitian coordinate to the
repository's skew-Hermitian matrix coordinate. -/
def cmp98Eq121FromPrintedMatrix
    (h : Matrix (Fin Nc) (Fin Nc) ℂ) : Matrix (Fin Nc) (Fin Nc) ℂ :=
  (Complex.I : ℂ) • h

@[simp] theorem cmp98Eq121FromPrintedMatrix_toPrinted
    (H : Matrix (Fin Nc) (Fin Nc) ℂ) :
    cmp98Eq121FromPrintedMatrix (cmp98Eq121ToPrintedMatrix H) = H := by
  simp [cmp98Eq121FromPrintedMatrix, cmp98Eq121ToPrintedMatrix, smul_smul]

@[simp] theorem cmp98Eq121ToPrintedMatrix_fromPrinted
    (h : Matrix (Fin Nc) (Fin Nc) ℂ) :
    cmp98Eq121ToPrintedMatrix (cmp98Eq121FromPrintedMatrix h) = h := by
  simp [cmp98Eq121FromPrintedMatrix, cmp98Eq121ToPrintedMatrix, smul_smul]

/-- The earlier Lie-coordinate definition is exactly the generic `1/i`
matrix conversion. -/
theorem cmp98Eq121PrintedLieCoordMatrix_eq_toPrinted
    (X : SUNLieCoord Nc) :
    cmp98Eq121PrintedLieCoordMatrix X =
      cmp98Eq121ToPrintedMatrix (cmp98LieCoordMatrix X) := by
  rfl

/-- **Printed `g(-i ad y)`.**  This is the exact coordinate transport of the
right-trivialized exponential derivative.  Both the minus sign in the
repository argument and the two visible factors of `i` are part of the
definition forced by CMP98 (32), (33), and (121). -/
def cmp98Eq121PrintedGMinusIAd
    (y h : Matrix (Fin Nc) (Fin Nc) ℂ) : Matrix (Fin Nc) (Fin Nc) ℂ :=
  cmp98Eq121ToPrintedMatrix
    (cmp98GAd (-(cmp98Eq121FromPrintedMatrix y))
      (cmp98Eq121FromPrintedMatrix h))

/-- Exact conjugacy between the source right frame and Balaban's printed
`g(-i ad y)` coordinates. -/
theorem cmp98Eq121PrintedGMinusIAd_toPrinted
    (Y H : Matrix (Fin Nc) (Fin Nc) ℂ) :
    cmp98Eq121PrintedGMinusIAd
        (cmp98Eq121ToPrintedMatrix Y) (cmp98Eq121ToPrintedMatrix H) =
      cmp98Eq121ToPrintedMatrix (cmp98GAd (-Y) H) := by
  simp [cmp98Eq121PrintedGMinusIAd]

/-- The four lines of CMP98 (124), now literally in the Hermitian coordinate
normalization printed in (121). -/
def cmp98Eq124PrintedHermitianFourLinePhysicalVariation
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N') : Matrix (Fin Nc) (Fin Nc) ℂ :=
  cmp98Eq121ToPrintedMatrix
    (cmp98Eq124RightPrintedFourLinePhysicalVariation U A b)

/-- Terminal `(118)--(121) → (124)` statement with the source's visible
`1/i` normalization and the right-frame sign fixed internally. -/
theorem cmp98Eq121ToPrinted_deriv_cmp98Eq120SourceCurve_zero_eq_fourLine
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N')
    (hthird : ∀ x ∈ blockOf M N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix U b x 0‖ ≤ 1 / 3) :
    cmp98Eq121ToPrintedMatrix (deriv (cmp98Eq120SourceCurve U A b) 0) =
      cmp98Eq124PrintedHermitianFourLinePhysicalVariation U A b := by
  rw [deriv_cmp98Eq120SourceCurve_zero_eq_fourLine U A b hthird]
  rfl

end

end YangMills.RG
