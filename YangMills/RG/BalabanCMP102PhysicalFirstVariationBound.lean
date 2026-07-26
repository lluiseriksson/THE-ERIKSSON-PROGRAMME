/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP102PhysicalTwoFieldCorrection

/-!
# Source-sup-norm bounds for the physical CMP98 first variations

This module begins the remaining linear estimate in the CMP102 contraction
argument.  A single physical edge variation is bounded by the source field
sup norm.  The literal contour recursion then costs exactly one copy per
edge.  Finally the four-factor `Ubar` derivative is identified with the
derivative of the concatenated source contour and receives the
volume-independent length bound `2(d+1)M`.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {d M N' Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero N'] [NeZero Nc]

/-- One oriented physical edge first variation at the background is bounded
by the source field sup norm. -/
theorem norm_orientedWilsonFactorFirst_zero_le_sourceSupNorm
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (e : ConcreteEdge d (M * N')) :
    ‖orientedWilsonFactorFirst U A e 0‖ ≤
      cmp98SourceFieldSupNorm A := by
  have hgen :=
    norm_orientedWilsonGenerator_le_cmp98SourceFieldSupNorm A e
  cases h : e.sign
  · simp only [orientedWilsonFactorFirst, h, Bool.false_eq_true, if_false,
      physicalMatrixExp_zero_smul, one_mul]
    calc
      ‖Matrix.conjTranspose (orientedWilsonPositiveBase U e) *
          orientedWilsonGenerator A e‖
          ≤ ‖Matrix.conjTranspose (orientedWilsonPositiveBase U e)‖ *
              ‖orientedWilsonGenerator A e‖ := norm_mul_le _ _
      _ = ‖orientedWilsonGenerator A e‖ := by
        rw [Matrix.l2_opNorm_conjTranspose,
          norm_orientedWilsonPositiveBase, one_mul]
      _ ≤ _ := hgen
  · simp only [orientedWilsonFactorFirst, h, if_true,
      physicalMatrixExp_zero_smul, one_mul]
    calc
      ‖orientedWilsonGenerator A e * orientedWilsonPositiveBase U e‖
          ≤ ‖orientedWilsonGenerator A e‖ *
              ‖orientedWilsonPositiveBase U e‖ := norm_mul_le _ _
      _ = ‖orientedWilsonGenerator A e‖ := by
        rw [norm_orientedWilsonPositiveBase, mul_one]
      _ ≤ _ := hgen

/-- The background first variation of an arbitrary literal contour is
linear in its literal path length. -/
theorem norm_cmp98ContourFirstVariation_zero_le_sourceSupNorm
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (es : List (ConcreteEdge d (M * N'))) :
    ‖cmp98ContourFirstVariation U A es 0‖ ≤
      (es.length : ℝ) * cmp98SourceFieldSupNorm A := by
  let S := cmp98SourceFieldSupNorm A
  have hS : 0 ≤ S := cmp98SourceFieldSupNorm_nonneg A
  induction es with
  | nil =>
      simp [cmp98ContourFirstVariation]
  | cons e es ih =>
      rw [cmp98ContourFirstVariation]
      calc
        ‖orientedWilsonFactorFirst U A e 0 *
              cmp98ContourMatrixCurve U A es 0 +
            orientedWilsonFactor U A e 0 *
              cmp98ContourFirstVariation U A es 0‖
            ≤ ‖orientedWilsonFactorFirst U A e 0 *
                  cmp98ContourMatrixCurve U A es 0‖ +
                ‖orientedWilsonFactor U A e 0 *
                  cmp98ContourFirstVariation U A es 0‖ :=
          norm_add_le _ _
        _ ≤ S + (es.length : ℝ) * S := by
          apply add_le_add
          · calc
              ‖orientedWilsonFactorFirst U A e 0 *
                    cmp98ContourMatrixCurve U A es 0‖
                  ≤ ‖orientedWilsonFactorFirst U A e 0‖ *
                      ‖cmp98ContourMatrixCurve U A es 0‖ :=
                norm_mul_le _ _
              _ = ‖orientedWilsonFactorFirst U A e 0‖ := by
                rw [norm_cmp98ContourMatrixCurve_eq_one, mul_one]
              _ ≤ S :=
                norm_orientedWilsonFactorFirst_zero_le_sourceSupNorm U A e
          · calc
              ‖orientedWilsonFactor U A e 0 *
                    cmp98ContourFirstVariation U A es 0‖
                  ≤ ‖orientedWilsonFactor U A e 0‖ *
                      ‖cmp98ContourFirstVariation U A es 0‖ :=
                norm_mul_le _ _
              _ = ‖cmp98ContourFirstVariation U A es 0‖ := by
                rw [norm_orientedWilsonFactor_eq_one, one_mul]
              _ ≤ (es.length : ℝ) * S := ih
        _ = ((e :: es).length : ℝ) * S := by
          simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
          ring

/-- The first variation of the literal four-factor `Ubar` deviation is
exactly the first variation of the concatenated source contour. -/
theorem cmp98UbarDeviationFirstVariation_zero_eq_sourceContour
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N') (x : FinBox d (M * N')) :
    cmp98UbarDeviationFirstVariation U A b x 0 =
      cmp98ContourFirstVariation U A
        (cmp98SourceFourContourEdges (Nc := Nc) b x) 0 := by
  have hdev := hasDerivAt_cmp98UbarDeviationCurve U A b x 0
  have hcont := hasDerivAt_cmp98ContourMatrixCurve U A
    (cmp98SourceFourContourEdges (Nc := Nc) b x) 0
  have heq :
      cmp98UbarDeviationCurve U A b x =
        fun t => cmp98ContourMatrixCurve U A
          (cmp98SourceFourContourEdges (Nc := Nc) b x) t - 1 := by
    funext t
    unfold cmp98UbarDeviationCurve
    rw [cmp98UbarFourFactorProduct_eq_sourceContourMatrixCurve]
  have hsource :
      HasDerivAt (cmp98UbarDeviationCurve U A b x)
        (cmp98ContourFirstVariation U A
          (cmp98SourceFourContourEdges (Nc := Nc) b x) 0) 0 := by
    rw [heq]
    exact hcont.sub_const 1
  exact hdev.unique hsource

/-- The local `Ubar` deviation derivative has the physical source-length
bound and is independent of the periodic volume. -/
theorem norm_cmp98UbarDeviationFirstVariation_zero_le_sourceScale
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N') (x : FinBox d (M * N'))
    (hx : x ∈ blockOf M N' b.1) :
    ‖cmp98UbarDeviationFirstVariation U A b x 0‖ ≤
      ((2 * (d + 1) * M : ℕ) : ℝ) *
        cmp98SourceFieldSupNorm A := by
  rw [cmp98UbarDeviationFirstVariation_zero_eq_sourceContour]
  have hraw := norm_cmp98ContourFirstVariation_zero_le_sourceSupNorm
    U A (cmp98SourceFourContourEdges (Nc := Nc) b x)
  have hlen :
      ((cmp98SourceFourContourEdges (Nc := Nc) b x).length : ℝ) ≤
        ((2 * (d + 1) * M : ℕ) : ℝ) := by
    exact_mod_cast cmp98SourceFourContourEdges_length_le
      (Nc := Nc) b x hx
  exact hraw.trans (mul_le_mul_of_nonneg_right hlen
    (cmp98SourceFieldSupNorm_nonneg A))

/-- The literal coarse right variation is bounded by its exact straight-path
length `M`. -/
theorem norm_cmp98Eq119CoarseRightVariation_le_sourceScale
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N') :
    ‖cmp98Eq119CoarseRightVariation U A b‖ ≤
      (M : ℝ) * cmp98SourceFieldSupNorm A := by
  unfold cmp98Eq119CoarseRightVariation
  calc
    ‖cmp98ContourFirstVariation U A
          (cmp98SourceCoarseBondPath (Nc := Nc) b) 0 *
        Matrix.conjTranspose
          (cmp98ContourMatrixCurve U A
            (cmp98SourceCoarseBondPath (Nc := Nc) b) 0)‖
        ≤ ‖cmp98ContourFirstVariation U A
              (cmp98SourceCoarseBondPath (Nc := Nc) b) 0‖ *
            ‖Matrix.conjTranspose
              (cmp98ContourMatrixCurve U A
                (cmp98SourceCoarseBondPath (Nc := Nc) b) 0)‖ :=
      norm_mul_le _ _
    _ = ‖cmp98ContourFirstVariation U A
          (cmp98SourceCoarseBondPath (Nc := Nc) b) 0‖ := by
      rw [Matrix.l2_opNorm_conjTranspose,
        norm_cmp98ContourMatrixCurve_eq_one, mul_one]
    _ ≤ ((cmp98SourceCoarseBondPath
          (Nc := Nc) b).length : ℝ) * cmp98SourceFieldSupNorm A :=
      norm_cmp98ContourFirstVariation_zero_le_sourceSupNorm U A _
    _ = (M : ℝ) * cmp98SourceFieldSupNorm A := by
      rw [cmp98SourceCoarseBondPath_length (Nc := Nc)]

end

end YangMills.RG
