/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP102AmbientNonlinearBlockFDeriv
import YangMills.RG.BalabanCMP102AmbientWilsonLineFDerivBound

/-!
# Generated contour budgets for the CMP102 represented block

The represented-block product rule previously accepted value, derivative,
value-Lipschitz, and derivative-Lipschitz bounds for the straight coarse
Wilson contour.  This module generates all four from the literal source path
and the audited finite Wilson-line recurrences.

Only the outer logarithmic-exponential factor remains as a separate analytic
producer.
-/

namespace YangMills.RG

open Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {d M N' Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero N'] [NeZero Nc]

/-- Literal value budget of the straight source coarse-bond contour. -/
def cmp102SourceCoarseContourValueBudget
    (M : ℕ) (r : ℝ) : ℝ :=
  cmp98AmbientWilsonLineValueBudget r M

/-- Literal derivative budget of the straight source coarse-bond contour. -/
def cmp102SourceCoarseContourDerivativeBudget
    (M : ℕ) (r : ℝ) : ℝ :=
  cmp98AmbientWilsonLineDerivativeBudget r M

/-- Literal value-Lipschitz budget of the straight source contour. -/
def cmp102SourceCoarseContourValueLipschitzBudget
    (M : ℕ) (r : ℝ) : ℝ :=
  cmp98AmbientWilsonLineValueLipschitzBudget r M

/-- Literal derivative-Lipschitz budget of the straight source contour. -/
def cmp102SourceCoarseContourDerivativeLipschitzBudget
    (M : ℕ) (r : ℝ) : ℝ :=
  cmp98AmbientWilsonLineDerivativeLipschitzBudget r M

/-- The represented-block derivative bound with both straight-contour
constants generated internally from the source path. -/
theorem norm_fderiv_cmp102AmbientNonlinearBlock_le_of_generatedContour
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (b : PhysicalBond d N')
    (Z : PhysicalAmbientMatrixTangent d (M * N') Nc)
    {r DE E : ℝ}
    (hr : 0 ≤ r) (hZ : ‖Z‖ ≤ r)
    (hlocal : ∀ x ∈ blockOf M N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix U b x Z‖ < 1)
    (hDE : ‖fderiv ℝ (cmp98UbarExpAverage U b) Z‖ ≤ DE)
    (hE : ‖cmp98UbarExpAverage U b Z‖ ≤ E) :
    ‖fderiv ℝ (cmp102AmbientNonlinearBlock U b) Z‖ ≤
      cmp102AmbientNonlinearBlockDerivativeBudget
        DE (cmp102SourceCoarseContourValueBudget M r)
        E (cmp102SourceCoarseContourDerivativeBudget M r) := by
  have hpath :
      ∀ e ∈ cmp98SourceCoarseBondPath (Nc := Nc) b,
        ‖Z (physicalBondOfEdge e)‖ ≤ r := by
    intro e _
    exact (norm_physicalAmbientMatrixTangent_apply_le Z
      (physicalBondOfEdge e)).trans hZ
  apply norm_fderiv_cmp102AmbientNonlinearBlock_le
    U b Z hlocal hDE
  · simpa only [cmp102SourceCoarseContourValueBudget,
      cmp98SourceCoarseBondPath_length] using
      (norm_cmp98AmbientWilsonLineMatrix_le U Z
        (cmp98SourceCoarseBondPath (Nc := Nc) b) hr hpath)
  · exact hE
  · simpa only [cmp102SourceCoarseContourDerivativeBudget,
      cmp98SourceCoarseBondPath_length] using
      (norm_fderiv_cmp98AmbientWilsonLineMatrix_le U Z
        (cmp98SourceCoarseBondPath (Nc := Nc) b) hr hpath)

/-- The represented-block derivative-Lipschitz bound with all four
straight-contour obligations generated internally. -/
theorem norm_fderiv_cmp102AmbientNonlinearBlock_sub_le_of_generatedContour
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (b : PhysicalBond d N')
    (Z W : PhysicalAmbientMatrixTangent d (M * N') Nc)
    {r DDE DE LE E : ℝ}
    (hr : 0 ≤ r) (hZ : ‖Z‖ ≤ r) (hW : ‖W‖ ≤ r)
    (hlocalZ : ∀ x ∈ blockOf M N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix U b x Z‖ < 1)
    (hlocalW : ∀ x ∈ blockOf M N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix U b x W‖ < 1)
    (hDDE : 0 ≤ DDE) (hLE : 0 ≤ LE)
    (hDE : ‖fderiv ℝ (cmp98UbarExpAverage U b) W‖ ≤ DE)
    (hE : ‖cmp98UbarExpAverage U b W‖ ≤ E)
    (hDDEbound :
      ‖fderiv ℝ (cmp98UbarExpAverage U b) Z -
          fderiv ℝ (cmp98UbarExpAverage U b) W‖ ≤ DDE * ‖Z - W‖)
    (hLEbound :
      ‖cmp98UbarExpAverage U b Z - cmp98UbarExpAverage U b W‖ ≤
        LE * ‖Z - W‖) :
    ‖fderiv ℝ (cmp102AmbientNonlinearBlock U b) Z -
        fderiv ℝ (cmp102AmbientNonlinearBlock U b) W‖ ≤
      cmp102AmbientNonlinearBlockDerivativeLipschitzBudget
        DDE
        (cmp102SourceCoarseContourValueBudget M r)
        DE
        (cmp102SourceCoarseContourValueLipschitzBudget M r)
        LE
        (cmp102SourceCoarseContourDerivativeBudget M r)
        E
        (cmp102SourceCoarseContourDerivativeLipschitzBudget M r) *
          ‖Z - W‖ := by
  have hZpath :
      ∀ e ∈ cmp98SourceCoarseBondPath (Nc := Nc) b,
        ‖Z (physicalBondOfEdge e)‖ ≤ r := by
    intro e _
    exact (norm_physicalAmbientMatrixTangent_apply_le Z
      (physicalBondOfEdge e)).trans hZ
  have hWpath :
      ∀ e ∈ cmp98SourceCoarseBondPath (Nc := Nc) b,
        ‖W (physicalBondOfEdge e)‖ ≤ r := by
    intro e _
    exact (norm_physicalAmbientMatrixTangent_apply_le W
      (physicalBondOfEdge e)).trans hW
  apply norm_fderiv_cmp102AmbientNonlinearBlock_sub_le
    U b Z W hlocalZ hlocalW hDDE
    (cmp98AmbientWilsonLineValueLipschitzBudget_nonneg hr _)
    hLE
    (cmp98AmbientWilsonLineDerivativeLipschitzBudget_nonneg hr _)
    hDE
  · simpa only [cmp102SourceCoarseContourValueBudget,
      cmp98SourceCoarseBondPath_length] using
      (norm_cmp98AmbientWilsonLineMatrix_le U Z
        (cmp98SourceCoarseBondPath (Nc := Nc) b) hr hZpath)
  · exact hE
  · simpa only [cmp102SourceCoarseContourDerivativeBudget,
      cmp98SourceCoarseBondPath_length] using
      (norm_fderiv_cmp98AmbientWilsonLineMatrix_le U Z
        (cmp98SourceCoarseBondPath (Nc := Nc) b) hr hZpath)
  · exact hDDEbound
  · simpa only [cmp102SourceCoarseContourValueLipschitzBudget,
      cmp98SourceCoarseBondPath_length] using
      (norm_cmp98AmbientWilsonLineMatrix_sub_le U Z W
        (cmp98SourceCoarseBondPath (Nc := Nc) b) hr hZpath hWpath)
  · exact hLEbound
  · simpa only [cmp102SourceCoarseContourDerivativeLipschitzBudget,
      cmp98SourceCoarseBondPath_length] using
      (norm_fderiv_cmp98AmbientWilsonLineMatrix_sub_le U Z W
        (cmp98SourceCoarseBondPath (Nc := Nc) b) hr hZpath hWpath)

end

end YangMills.RG
