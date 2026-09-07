/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP102PhysicalTwoFieldExponential
import YangMills.RG.BalabanCMP98Eq123LogBound

/-!
# Two-field Lipschitz control for physical CMP98 contours

The preceding source-faithful checkpoint controls the physical exponential
on one oriented edge.  Here that estimate is propagated through the literal
ordered contour product.

The proof follows the contour recursion itself.  Every oriented factor and
every remaining contour has L2 operator norm exactly one, so telescoping
costs precisely one copy of the edge estimate per contour edge.  The result
is linear in the literal contour length and independent of the ambient
volume.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {d M N' Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero N'] [NeZero Nc]

/-- Every literal oriented factor along the physical chart has norm one. -/
theorem norm_orientedWilsonFactor_eq_one
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (e : ConcreteEdge d (M * N')) (t : ℝ) :
    ‖orientedWilsonFactor U A e t‖ = 1 := by
  simpa [cmp98ContourMatrixCurve] using
    (norm_cmp98ContourMatrixCurve_eq_one U A [e] t)

/-- The source-explicit exponential estimate transports through the fixed
unitary background factor, with no loss for either edge orientation. -/
theorem norm_orientedWilsonFactor_sub_le
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A B : PhysicalGaugeOneCochain d (M * N') Nc)
    (e : ConcreteEdge d (M * N')) (t r : ℝ)
    (hr : 0 ≤ r)
    (hA : |t| * cmp98SourceFieldSupNorm A ≤ r)
    (hB : |t| * cmp98SourceFieldSupNorm B ≤ r) :
    ‖orientedWilsonFactor U A e t -
        orientedWilsonFactor U B e t‖ ≤
      cmp102ExpLipschitzBudget r *
        (|t| * cmp98SourceFieldSupNorm (A - B)) := by
  have hexp :=
    norm_physicalMatrixExp_orientedGenerator_sub_le
      A B e t r hr hA hB
  cases h : e.sign
  · simp only [orientedWilsonFactor, h, Bool.false_eq_true, if_false,
      ← mul_sub]
    calc
      ‖Matrix.conjTranspose (orientedWilsonPositiveBase U e) *
          (physicalMatrixExp (t • orientedWilsonGenerator A e) -
            physicalMatrixExp (t • orientedWilsonGenerator B e))‖
          ≤ ‖Matrix.conjTranspose (orientedWilsonPositiveBase U e)‖ *
              ‖physicalMatrixExp (t • orientedWilsonGenerator A e) -
                physicalMatrixExp (t • orientedWilsonGenerator B e)‖ :=
        norm_mul_le _ _
      _ = ‖physicalMatrixExp (t • orientedWilsonGenerator A e) -
            physicalMatrixExp (t • orientedWilsonGenerator B e)‖ := by
        rw [Matrix.l2_opNorm_conjTranspose,
          norm_orientedWilsonPositiveBase, one_mul]
      _ ≤ _ := hexp
  · simp only [orientedWilsonFactor, h, if_true, ← sub_mul]
    calc
      ‖(physicalMatrixExp (t • orientedWilsonGenerator A e) -
            physicalMatrixExp (t • orientedWilsonGenerator B e)) *
          orientedWilsonPositiveBase U e‖
          ≤ ‖physicalMatrixExp (t • orientedWilsonGenerator A e) -
                physicalMatrixExp (t • orientedWilsonGenerator B e)‖ *
              ‖orientedWilsonPositiveBase U e‖ :=
        norm_mul_le _ _
      _ = ‖physicalMatrixExp (t • orientedWilsonGenerator A e) -
            physicalMatrixExp (t • orientedWilsonGenerator B e)‖ := by
        rw [norm_orientedWilsonPositiveBase, mul_one]
      _ ≤ _ := hexp

/-- The two-field contour displacement is linear in the literal path length.
No ambient-volume cardinality enters the bound. -/
theorem norm_cmp98ContourMatrixCurve_sub_le
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A B : PhysicalGaugeOneCochain d (M * N') Nc)
    (es : List (ConcreteEdge d (M * N'))) (t r : ℝ)
    (hr : 0 ≤ r)
    (hA : |t| * cmp98SourceFieldSupNorm A ≤ r)
    (hB : |t| * cmp98SourceFieldSupNorm B ≤ r) :
    ‖cmp98ContourMatrixCurve U A es t -
        cmp98ContourMatrixCurve U B es t‖ ≤
      (es.length : ℝ) *
        (cmp102ExpLipschitzBudget r *
          (|t| * cmp98SourceFieldSupNorm (A - B))) := by
  let L := cmp102ExpLipschitzBudget r *
    (|t| * cmp98SourceFieldSupNorm (A - B))
  have hL : 0 ≤ L := by
    exact mul_nonneg (cmp102ExpLipschitzBudget_nonneg r hr)
      (mul_nonneg (abs_nonneg t)
        (cmp98SourceFieldSupNorm_nonneg (A - B)))
  induction es with
  | nil =>
      simp [cmp98ContourMatrixCurve]
  | cons e es ih =>
      rw [cmp98ContourMatrixCurve, cmp98ContourMatrixCurve]
      rw [twoFactor_sub_zero_eq]
      calc
        ‖(orientedWilsonFactor U A e t -
              orientedWilsonFactor U B e t) *
              cmp98ContourMatrixCurve U A es t +
            orientedWilsonFactor U B e t *
              (cmp98ContourMatrixCurve U A es t -
                cmp98ContourMatrixCurve U B es t)‖
            ≤ ‖(orientedWilsonFactor U A e t -
                  orientedWilsonFactor U B e t) *
                  cmp98ContourMatrixCurve U A es t‖ +
                ‖orientedWilsonFactor U B e t *
                  (cmp98ContourMatrixCurve U A es t -
                    cmp98ContourMatrixCurve U B es t)‖ :=
          norm_add_le _ _
        _ ≤ L + (es.length : ℝ) * L := by
          apply add_le_add
          · calc
              ‖(orientedWilsonFactor U A e t -
                    orientedWilsonFactor U B e t) *
                    cmp98ContourMatrixCurve U A es t‖
                  ≤ ‖orientedWilsonFactor U A e t -
                        orientedWilsonFactor U B e t‖ *
                      ‖cmp98ContourMatrixCurve U A es t‖ :=
                norm_mul_le _ _
              _ = ‖orientedWilsonFactor U A e t -
                    orientedWilsonFactor U B e t‖ := by
                rw [norm_cmp98ContourMatrixCurve_eq_one, mul_one]
              _ ≤ L := by
                exact norm_orientedWilsonFactor_sub_le
                  U A B e t r hr hA hB
          · calc
              ‖orientedWilsonFactor U B e t *
                    (cmp98ContourMatrixCurve U A es t -
                      cmp98ContourMatrixCurve U B es t)‖
                  ≤ ‖orientedWilsonFactor U B e t‖ *
                      ‖cmp98ContourMatrixCurve U A es t -
                        cmp98ContourMatrixCurve U B es t‖ :=
                norm_mul_le _ _
              _ = ‖cmp98ContourMatrixCurve U A es t -
                    cmp98ContourMatrixCurve U B es t‖ := by
                rw [norm_orientedWilsonFactor_eq_one, one_mul]
              _ ≤ (es.length : ℝ) * L := ih
        _ = ((e :: es).length : ℝ) * L := by
          simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
          ring

/-- Source-scale specialization for the literal four-contour word.  The
constant is linear in the block scale and independent of the periodic
volume. -/
theorem norm_cmp98SourceFourContourMatrixCurve_sub_le_sourceScale
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A B : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N') (x : FinBox d (M * N'))
    (hx : x ∈ blockOf M N' b.1)
    (t r : ℝ)
    (hr : 0 ≤ r)
    (hA : |t| * cmp98SourceFieldSupNorm A ≤ r)
    (hB : |t| * cmp98SourceFieldSupNorm B ≤ r) :
    ‖cmp98ContourMatrixCurve U A
          (cmp98SourceFourContourEdges (Nc := Nc) b x) t -
        cmp98ContourMatrixCurve U B
          (cmp98SourceFourContourEdges (Nc := Nc) b x) t‖ ≤
      ((2 * (d + 1) * M : ℕ) : ℝ) *
        (cmp102ExpLipschitzBudget r *
          (|t| * cmp98SourceFieldSupNorm (A - B))) := by
  have hraw := norm_cmp98ContourMatrixCurve_sub_le U A B
    (cmp98SourceFourContourEdges (Nc := Nc) b x) t r hr hA hB
  have hlen :
      (cmp98SourceFourContourEdges (Nc := Nc) b x).length ≤
        2 * (d + 1) * M :=
    cmp98SourceFourContourEdges_length_le (Nc := Nc) b x hx
  have hcast :
      ((cmp98SourceFourContourEdges (Nc := Nc) b x).length : ℝ) ≤
        ((2 * (d + 1) * M : ℕ) : ℝ) := by
    exact_mod_cast hlen
  exact hraw.trans (mul_le_mul_of_nonneg_right hcast
    (mul_nonneg (cmp102ExpLipschitzBudget_nonneg r hr)
      (mul_nonneg (abs_nonneg t)
        (cmp98SourceFieldSupNorm_nonneg (A - B)))))

end

end YangMills.RG
