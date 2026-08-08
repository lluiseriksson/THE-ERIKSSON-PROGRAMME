/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP102AmbientFourContourCollapse

/-!
# Uniform source-length budgets for the CMP98 four-contour deviation

The source word through a block point has length at most
`2 * (d + 1) * M`.  This module proves that every recursive ambient
Wilson-line budget is monotone in the word length and hence replaces the
point-dependent length by that literal source bound.

The resulting four estimates are uniform in the periodic volume and accept
only a global ambient-radius hypothesis.
-/

namespace YangMills.RG

open Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {d M N' Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero N'] [NeZero Nc]

/-- The one-edge value budget is at least one on a nonnegative radius. -/
theorem one_le_cmp102AmbientEdgeValueBudget
    {r : ℝ} (hr : 0 ≤ r) :
    1 ≤ cmp102AmbientEdgeValueBudget r := by
  unfold cmp102AmbientEdgeValueBudget
  have hB₂ := expSecondDerivativeBudget_nonneg r hr
  have hB₁ := expDerivativeBudget_nonneg r hr
  have h₂ : 0 ≤ expSecondDerivativeBudget r * r ^ 2 :=
    mul_nonneg hB₂ (sq_nonneg r)
  have h₁ : 0 ≤ expDerivativeBudget r * r :=
    mul_nonneg hB₁ hr
  linarith

/-- Wilson-line value budgets are monotone in the word length. -/
theorem cmp98AmbientWilsonLineValueBudget_monotone
    {r : ℝ} (hr : 0 ≤ r) :
    Monotone (cmp98AmbientWilsonLineValueBudget r) := by
  apply monotone_nat_of_le_succ
  intro n
  rw [cmp98AmbientWilsonLineValueBudget]
  calc
    cmp98AmbientWilsonLineValueBudget r n
        = 1 * cmp98AmbientWilsonLineValueBudget r n := by ring
    _ ≤ cmp102AmbientEdgeValueBudget r *
          cmp98AmbientWilsonLineValueBudget r n :=
      mul_le_mul_of_nonneg_right
        (one_le_cmp102AmbientEdgeValueBudget hr)
        (cmp98AmbientWilsonLineValueBudget_nonneg hr n)

/-- Wilson-line value-Lipschitz budgets are monotone in the word length. -/
theorem cmp98AmbientWilsonLineValueLipschitzBudget_monotone
    {r : ℝ} (hr : 0 ≤ r) :
    Monotone (cmp98AmbientWilsonLineValueLipschitzBudget r) := by
  apply monotone_nat_of_le_succ
  intro n
  rw [cmp98AmbientWilsonLineValueLipschitzBudget]
  have hL :=
    cmp98AmbientWilsonLineValueLipschitzBudget_nonneg hr n
  have hV := cmp98AmbientWilsonLineValueBudget_nonneg hr n
  have hEdgeL := cmp102AmbientEdgeValueLipschitzBudget_nonneg hr
  calc
    cmp98AmbientWilsonLineValueLipschitzBudget r n
        = 1 * cmp98AmbientWilsonLineValueLipschitzBudget r n := by ring
    _ ≤ cmp102AmbientEdgeValueBudget r *
          cmp98AmbientWilsonLineValueLipschitzBudget r n :=
      mul_le_mul_of_nonneg_right
        (one_le_cmp102AmbientEdgeValueBudget hr) hL
    _ ≤ cmp102AmbientEdgeValueLipschitzBudget r *
            cmp98AmbientWilsonLineValueBudget r n +
          cmp102AmbientEdgeValueBudget r *
            cmp98AmbientWilsonLineValueLipschitzBudget r n :=
      le_add_of_nonneg_left (mul_nonneg hEdgeL hV)

/-- Wilson-line derivative budgets are monotone in the word length. -/
theorem cmp98AmbientWilsonLineDerivativeBudget_monotone
    {r : ℝ} (hr : 0 ≤ r) :
    Monotone (cmp98AmbientWilsonLineDerivativeBudget r) := by
  apply monotone_nat_of_le_succ
  intro n
  rw [cmp98AmbientWilsonLineDerivativeBudget]
  have hD := cmp98AmbientWilsonLineDerivativeBudget_nonneg hr n
  have hV := cmp98AmbientWilsonLineValueBudget_nonneg hr n
  have hB₁ := expDerivativeBudget_nonneg r hr
  calc
    cmp98AmbientWilsonLineDerivativeBudget r n
        = 1 * cmp98AmbientWilsonLineDerivativeBudget r n := by ring
    _ ≤ cmp102AmbientEdgeValueBudget r *
          cmp98AmbientWilsonLineDerivativeBudget r n :=
      mul_le_mul_of_nonneg_right
        (one_le_cmp102AmbientEdgeValueBudget hr) hD
    _ ≤ expDerivativeBudget r *
            cmp98AmbientWilsonLineValueBudget r n +
          cmp102AmbientEdgeValueBudget r *
            cmp98AmbientWilsonLineDerivativeBudget r n :=
      le_add_of_nonneg_left (mul_nonneg hB₁ hV)

/-- Wilson-line derivative-Lipschitz budgets are monotone in word length. -/
theorem cmp98AmbientWilsonLineDerivativeLipschitzBudget_monotone
    {r : ℝ} (hr : 0 ≤ r) :
    Monotone (cmp98AmbientWilsonLineDerivativeLipschitzBudget r) := by
  apply monotone_nat_of_le_succ
  intro n
  rw [cmp98AmbientWilsonLineDerivativeLipschitzBudget]
  have hH :=
    cmp98AmbientWilsonLineDerivativeLipschitzBudget_nonneg hr n
  have hV := cmp98AmbientWilsonLineValueBudget_nonneg hr n
  have hL :=
    cmp98AmbientWilsonLineValueLipschitzBudget_nonneg hr n
  have hD := cmp98AmbientWilsonLineDerivativeBudget_nonneg hr n
  have hB₂ := expSecondDerivativeBudget_nonneg r hr
  have hB₁ := expDerivativeBudget_nonneg r hr
  have hEdgeL := cmp102AmbientEdgeValueLipschitzBudget_nonneg hr
  have hEdgeV := cmp102AmbientEdgeValueBudget_nonneg hr
  calc
    cmp98AmbientWilsonLineDerivativeLipschitzBudget r n
        = 1 * cmp98AmbientWilsonLineDerivativeLipschitzBudget r n := by ring
    _ ≤ cmp102AmbientEdgeValueBudget r *
          cmp98AmbientWilsonLineDerivativeLipschitzBudget r n :=
      mul_le_mul_of_nonneg_right
        (one_le_cmp102AmbientEdgeValueBudget hr) hH
    _ ≤
        expSecondDerivativeBudget r *
            cmp98AmbientWilsonLineValueBudget r n +
          expDerivativeBudget r *
            cmp98AmbientWilsonLineValueLipschitzBudget r n +
          cmp102AmbientEdgeValueLipschitzBudget r *
            cmp98AmbientWilsonLineDerivativeBudget r n +
          cmp102AmbientEdgeValueBudget r *
            cmp98AmbientWilsonLineDerivativeLipschitzBudget r n := by
      have h₁ := mul_nonneg hB₂ hV
      have h₂ := mul_nonneg hB₁ hL
      have h₃ := mul_nonneg hEdgeL hD
      linarith

/-- Literal maximal length of the source four-contour word. -/
def cmp102SourceFourContourMaxLength (d M : ℕ) : ℕ :=
  2 * (d + 1) * M

/-- Uniform value budget for the source local deviation. -/
def cmp102SourceFourContourDeviationValueBudget
    (d M : ℕ) (r : ℝ) : ℝ :=
  cmp98AmbientWilsonLineValueBudget r
      (cmp102SourceFourContourMaxLength d M) + 1

/-- Uniform derivative budget for the source local deviation. -/
def cmp102SourceFourContourDeviationDerivativeBudget
    (d M : ℕ) (r : ℝ) : ℝ :=
  cmp98AmbientWilsonLineDerivativeBudget r
    (cmp102SourceFourContourMaxLength d M)

/-- Uniform value-Lipschitz budget for the source local deviation. -/
def cmp102SourceFourContourDeviationValueLipschitzBudget
    (d M : ℕ) (r : ℝ) : ℝ :=
  cmp98AmbientWilsonLineValueLipschitzBudget r
    (cmp102SourceFourContourMaxLength d M)

/-- Uniform derivative-Lipschitz budget for the source local deviation. -/
def cmp102SourceFourContourDeviationDerivativeLipschitzBudget
    (d M : ℕ) (r : ℝ) : ℝ :=
  cmp98AmbientWilsonLineDerivativeLipschitzBudget r
    (cmp102SourceFourContourMaxLength d M)

/-- The local deviation value has a source-length budget independent of
the fine periodic volume. -/
theorem norm_cmp98UbarAmbientDeviationMatrix_le_sourceLengthBudget
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (b : PhysicalBond d N') (x : FinBox d (M * N'))
    (hx : x ∈ blockOf M N' b.1)
    (Z : PhysicalAmbientMatrixTangent d (M * N') Nc)
    {r : ℝ} (hr : 0 ≤ r) (hZ : ‖Z‖ ≤ r) :
    ‖cmp98UbarAmbientDeviationMatrix U b x Z‖ ≤
      cmp102SourceFourContourDeviationValueBudget d M r := by
  have hpath :
      ∀ e ∈ cmp98SourceFourContourEdges (Nc := Nc) b x,
        ‖Z (physicalBondOfEdge e)‖ ≤ r := by
    intro e _
    exact (norm_physicalAmbientMatrixTangent_apply_le Z _).trans hZ
  have hraw :=
    norm_cmp98UbarAmbientDeviationMatrix_le_lineBudget
      U b x Z hr hpath
  unfold cmp102SourceFourContourDeviationValueBudget
  exact hraw.trans (add_le_add
    (cmp98AmbientWilsonLineValueBudget_monotone hr
      (cmp98SourceFourContourEdges_length_le (Nc := Nc) b x hx))
    (le_refl 1))

/-- The local deviation derivative has the same uniform source length. -/
theorem norm_fderiv_cmp98UbarAmbientDeviationMatrix_le_sourceLengthBudget
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (b : PhysicalBond d N') (x : FinBox d (M * N'))
    (hx : x ∈ blockOf M N' b.1)
    (Z : PhysicalAmbientMatrixTangent d (M * N') Nc)
    {r : ℝ} (hr : 0 ≤ r) (hZ : ‖Z‖ ≤ r) :
    ‖fderiv ℝ (fun W => cmp98UbarAmbientDeviationMatrix U b x W) Z‖ ≤
      cmp102SourceFourContourDeviationDerivativeBudget d M r := by
  have hpath :
      ∀ e ∈ cmp98SourceFourContourEdges (Nc := Nc) b x,
        ‖Z (physicalBondOfEdge e)‖ ≤ r := by
    intro e _
    exact (norm_physicalAmbientMatrixTangent_apply_le Z _).trans hZ
  exact
    (norm_fderiv_cmp98UbarAmbientDeviationMatrix_le_lineBudget
      U b x Z hr hpath).trans
      (cmp98AmbientWilsonLineDerivativeBudget_monotone hr
        (cmp98SourceFourContourEdges_length_le (Nc := Nc) b x hx))

/-- The local deviation is uniformly Lipschitz on the ambient radius ball. -/
theorem norm_cmp98UbarAmbientDeviationMatrix_sub_le_sourceLengthBudget
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (b : PhysicalBond d N') (x : FinBox d (M * N'))
    (hx : x ∈ blockOf M N' b.1)
    (Z W : PhysicalAmbientMatrixTangent d (M * N') Nc)
    {r : ℝ} (hr : 0 ≤ r) (hZ : ‖Z‖ ≤ r) (hW : ‖W‖ ≤ r) :
    ‖cmp98UbarAmbientDeviationMatrix U b x Z -
        cmp98UbarAmbientDeviationMatrix U b x W‖ ≤
      cmp102SourceFourContourDeviationValueLipschitzBudget d M r *
        ‖Z - W‖ := by
  have hZpath :
      ∀ e ∈ cmp98SourceFourContourEdges (Nc := Nc) b x,
        ‖Z (physicalBondOfEdge e)‖ ≤ r := by
    intro e _
    exact (norm_physicalAmbientMatrixTangent_apply_le Z _).trans hZ
  have hWpath :
      ∀ e ∈ cmp98SourceFourContourEdges (Nc := Nc) b x,
        ‖W (physicalBondOfEdge e)‖ ≤ r := by
    intro e _
    exact (norm_physicalAmbientMatrixTangent_apply_le W _).trans hW
  have hraw :=
    norm_cmp98UbarAmbientDeviationMatrix_sub_le_lineBudget
      U b x Z W hr hZpath hWpath
  exact hraw.trans (mul_le_mul_of_nonneg_right
    (cmp98AmbientWilsonLineValueLipschitzBudget_monotone hr
      (cmp98SourceFourContourEdges_length_le (Nc := Nc) b x hx))
    (norm_nonneg _))

/-- The local deviation derivative is uniformly Lipschitz on the ambient
radius ball. -/
theorem norm_fderiv_cmp98UbarAmbientDeviationMatrix_sub_le_sourceLengthBudget
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (b : PhysicalBond d N') (x : FinBox d (M * N'))
    (hx : x ∈ blockOf M N' b.1)
    (Z W : PhysicalAmbientMatrixTangent d (M * N') Nc)
    {r : ℝ} (hr : 0 ≤ r) (hZ : ‖Z‖ ≤ r) (hW : ‖W‖ ≤ r) :
    ‖fderiv ℝ (fun V => cmp98UbarAmbientDeviationMatrix U b x V) Z -
        fderiv ℝ (fun V => cmp98UbarAmbientDeviationMatrix U b x V) W‖ ≤
      cmp102SourceFourContourDeviationDerivativeLipschitzBudget d M r *
        ‖Z - W‖ := by
  have hZpath :
      ∀ e ∈ cmp98SourceFourContourEdges (Nc := Nc) b x,
        ‖Z (physicalBondOfEdge e)‖ ≤ r := by
    intro e _
    exact (norm_physicalAmbientMatrixTangent_apply_le Z _).trans hZ
  have hWpath :
      ∀ e ∈ cmp98SourceFourContourEdges (Nc := Nc) b x,
        ‖W (physicalBondOfEdge e)‖ ≤ r := by
    intro e _
    exact (norm_physicalAmbientMatrixTangent_apply_le W _).trans hW
  have hraw :=
    norm_fderiv_cmp98UbarAmbientDeviationMatrix_sub_le_lineBudget
      U b x Z W hr hZpath hWpath
  exact hraw.trans (mul_le_mul_of_nonneg_right
    (cmp98AmbientWilsonLineDerivativeLipschitzBudget_monotone hr
      (cmp98SourceFourContourEdges_length_le (Nc := Nc) b x hx))
    (norm_nonneg _))

end

end YangMills.RG
