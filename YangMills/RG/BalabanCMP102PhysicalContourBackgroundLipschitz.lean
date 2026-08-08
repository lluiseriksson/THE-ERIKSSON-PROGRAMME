/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP102PhysicalFirstVariationBound
import YangMills.RG.BalabanCMP116WilsonOrientedEdgeMixedBounds

/-!
# Background Lipschitz bounds for physical CMP98 contours

This file compares the literal ordered contour and its first physical
variation with the same objects at the trivial background.  The estimates
are derived by induction over the source path.  In particular, the
first-variation estimate keeps the factor supplied by physical
small-background data; it does not assume a bound on the assembled CMP109
pivot defect.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {d M N' Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero N'] [NeZero Nc]

/-- A literal contour of length `m` changes by at most `m * ε` when every
oriented background factor is `ε`-close to its trivial value. -/
theorem norm_cmp98ContourMatrixCurve_zero_sub_trivial_le
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hsmall : PhysicalWilsonSmallBackground U ε)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (es : List (ConcreteEdge d (M * N'))) :
    ‖cmp98ContourMatrixCurve U A es 0 -
        cmp98ContourMatrixCurve
          (trivialPhysicalGaugeBackground d (M * N') Nc) A es 0‖ ≤
      (es.length : ℝ) * ε := by
  induction es with
  | nil =>
      simp [cmp98ContourMatrixCurve]
  | cons e es ih =>
      simp only [cmp98ContourMatrixCurve,
        orientedWilsonFactor_zero_eq_background]
      let U₀ := trivialPhysicalGaugeBackground d (M * N') Nc
      let F := orientedWilsonBackgroundFactor U e
      let F₀ := orientedWilsonBackgroundFactor U₀ e
      let C := cmp98ContourMatrixCurve U A es 0
      let C₀ := cmp98ContourMatrixCurve U₀ A es 0
      have hdecomp :
          F * C - F₀ * C₀ = (F - F₀) * C + F₀ * (C - C₀) := by
        noncomm_ring
      rw [hdecomp]
      calc
        ‖(F - F₀) * C + F₀ * (C - C₀)‖
            ≤ ‖(F - F₀) * C‖ + ‖F₀ * (C - C₀)‖ :=
          norm_add_le _ _
        _ ≤ ‖F - F₀‖ * ‖C‖ + ‖F₀‖ * ‖C - C₀‖ := by
          exact add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
        _ ≤ ε * 1 + 1 * ((es.length : ℝ) * ε) := by
          apply add_le_add
          · exact mul_le_mul
              (norm_orientedWilsonBackgroundFactor_sub_trivial_le
                U ε hsmall e)
              (le_of_eq (norm_cmp98ContourMatrixCurve_eq_one U A es 0))
              (norm_nonneg _)
              hε
          · exact mul_le_mul
              (le_of_eq (norm_orientedWilsonBackgroundFactor U₀ e))
              ih (norm_nonneg _) (by norm_num)
        _ = (((e :: es).length : ℕ) : ℝ) * ε := by
          simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
          ring

/-- The first variation of a length-`m` contour is background-Lipschitz with
the explicit quadratic path cost `m²`.  The extra factor of `m` is the
position of the differentiated edge inside the telescoping product. -/
theorem norm_cmp98ContourFirstVariation_zero_sub_trivial_le
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hsmall : PhysicalWilsonSmallBackground U ε)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (es : List (ConcreteEdge d (M * N'))) :
    ‖cmp98ContourFirstVariation U A es 0 -
        cmp98ContourFirstVariation
          (trivialPhysicalGaugeBackground d (M * N') Nc) A es 0‖ ≤
      (es.length : ℝ) ^ 2 * ε * cmp98SourceFieldSupNorm A := by
  let S := cmp98SourceFieldSupNorm A
  have hS : 0 ≤ S := cmp98SourceFieldSupNorm_nonneg A
  induction es with
  | nil =>
      simp [cmp98ContourFirstVariation]
  | cons e es ih =>
      simp only [cmp98ContourFirstVariation,
        orientedWilsonFactor_zero_eq_background]
      let U₀ := trivialPhysicalGaugeBackground d (M * N') Nc
      let F := orientedWilsonBackgroundFactor U e
      let F₀ := orientedWilsonBackgroundFactor U₀ e
      let G := orientedWilsonFactorFirst U A e 0
      let G₀ := orientedWilsonFactorFirst U₀ A e 0
      let C := cmp98ContourMatrixCurve U A es 0
      let C₀ := cmp98ContourMatrixCurve U₀ A es 0
      let D := cmp98ContourFirstVariation U A es 0
      let D₀ := cmp98ContourFirstVariation U₀ A es 0
      have hG :
          ‖G - G₀‖ ≤ ε * S := by
        calc
          ‖G - G₀‖
              ≤ ε * ‖orientedWilsonGenerator A e‖ :=
            norm_orientedWilsonFactorFirst_zero_sub_trivial_le
              U ε hsmall A e
          _ ≤ ε * S := by
            exact mul_le_mul_of_nonneg_left
              (norm_orientedWilsonGenerator_le_cmp98SourceFieldSupNorm A e) hε
      have hdecomp :
          (G * C + F * D) - (G₀ * C₀ + F₀ * D₀) =
            ((G - G₀) * C + G₀ * (C - C₀)) +
              ((F - F₀) * D + F₀ * (D - D₀)) := by
        noncomm_ring
      rw [hdecomp]
      calc
        ‖((G - G₀) * C + G₀ * (C - C₀)) +
              ((F - F₀) * D + F₀ * (D - D₀))‖
            ≤ (‖(G - G₀) * C‖ + ‖G₀ * (C - C₀)‖) +
                (‖(F - F₀) * D‖ + ‖F₀ * (D - D₀)‖) := by
          exact (norm_add_le _ _).trans
            (add_le_add (norm_add_le _ _) (norm_add_le _ _))
        _ ≤ (‖G - G₀‖ * ‖C‖ + ‖G₀‖ * ‖C - C₀‖) +
              (‖F - F₀‖ * ‖D‖ + ‖F₀‖ * ‖D - D₀‖) := by
          exact add_le_add
            (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))
            (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))
        _ ≤ (ε * S * 1 + S * ((es.length : ℝ) * ε)) +
              (ε * ((es.length : ℝ) * S) +
                1 * ((es.length : ℝ) ^ 2 * ε * S)) := by
          apply add_le_add
          · apply add_le_add
            · exact mul_le_mul
                hG
                (le_of_eq (norm_cmp98ContourMatrixCurve_eq_one U A es 0))
                (norm_nonneg _)
                (mul_nonneg hε hS)
            · exact mul_le_mul
                (norm_orientedWilsonFactorFirst_zero_le_sourceSupNorm
                  U₀ A e)
                (norm_cmp98ContourMatrixCurve_zero_sub_trivial_le
                  U ε hε hsmall A es)
                (norm_nonneg _)
                hS
          · apply add_le_add
            · exact mul_le_mul
                (norm_orientedWilsonBackgroundFactor_sub_trivial_le
                  U ε hsmall e)
                (norm_cmp98ContourFirstVariation_zero_le_sourceSupNorm
                  U A es)
                (norm_nonneg _)
                hε
            · exact mul_le_mul
                (le_of_eq (norm_orientedWilsonBackgroundFactor U₀ e))
                ih (norm_nonneg _)
                (by positivity)
        _ = (((e :: es).length : ℕ) : ℝ) ^ 2 * ε * S := by
          simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
          ring

end

end YangMills.RG
