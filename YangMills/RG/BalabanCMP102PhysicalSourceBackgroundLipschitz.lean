/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP102PhysicalContourBackgroundLipschitz
import YangMills.RG.BalabanCMP102PhysicalFirstVariationBound

/-!
# Source-specialized background Lipschitz bounds for CMP98

The generic contour estimates are specialized here to the literal
four-contour word printed in the CMP98 source construction.  Its physical
length is at most `2(d+1)M`, independently of the periodic volume.  Thus
both the background contour and its first variation acquire explicit
source-scale Lipschitz constants.

The tangent `A` in these estimates is the arbitrary physical one-cochain
inserted by the CMP109 pivot response.  It is not the Gaussian `bondField`
controlled by the CMP116 small-field cutoff.  Consequently this module does
not impose a cutoff estimate on `cmp98SourceFieldSupNorm A` and does not by
itself introduce a scalar smallness condition.  Such a condition may only be
read off after the pivot insertion, block normalization, flat calibration,
and right-inverse normalization have all been composed.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {d M N' Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero N'] [NeZero Nc]

/-- The literal four-factor background contour is Lipschitz at the trivial
background with the volume-independent source length `2(d+1)M`. -/
theorem norm_cmp98UbarFourFactorProduct_zero_sub_trivial_le_sourceScale
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hsmall : PhysicalWilsonSmallBackground U ε)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N') (x : FinBox d (M * N'))
    (hx : x ∈ blockOf M N' b.1) :
    ‖fourFactorProduct (cmp98UbarContourFactors U A b x) 0 -
        fourFactorProduct
          (cmp98UbarContourFactors
            (trivialPhysicalGaugeBackground d (M * N') Nc) A b x) 0‖ ≤
      ((2 * (d + 1) * M : ℕ) : ℝ) * ε := by
  rw [cmp98UbarFourFactorProduct_eq_sourceContourMatrixCurve,
    cmp98UbarFourFactorProduct_eq_sourceContourMatrixCurve]
  have hraw :=
    norm_cmp98ContourMatrixCurve_zero_sub_trivial_le
      U ε hε hsmall A (cmp98SourceFourContourEdges (Nc := Nc) b x)
  have hlen :
      ((cmp98SourceFourContourEdges (Nc := Nc) b x).length : ℝ) ≤
        ((2 * (d + 1) * M : ℕ) : ℝ) := by
    exact_mod_cast cmp98SourceFourContourEdges_length_le
      (Nc := Nc) b x hx
  exact hraw.trans (mul_le_mul_of_nonneg_right hlen hε)

/-- The matrix argument of the local Mercator logarithm inherits the same
background Lipschitz estimate at zero ambient tangent. -/
theorem norm_cmp98UbarAmbientDeviationMatrix_zero_sub_trivial_le_sourceScale
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hsmall : PhysicalWilsonSmallBackground U ε)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N') (x : FinBox d (M * N'))
    (hx : x ∈ blockOf M N' b.1) :
    ‖cmp98UbarAmbientDeviationMatrix U b x 0 -
        cmp98UbarAmbientDeviationMatrix
          (trivialPhysicalGaugeBackground d (M * N') Nc) b x 0‖ ≤
      ((2 * (d + 1) * M : ℕ) : ℝ) * ε := by
  have hU :
      cmp98UbarAmbientDeviationMatrix U b x 0 =
        cmp98UbarDeviationCurve U A b x 0 := by
    have hline :=
      cmp98UbarAmbientDeviationMatrix_line_eq_deviationCurve U A b x 0
    have hzero : (0 : ℝ) • physicalSuTangentToAmbient
        (physicalCochainToSuMatrixTangent A) = 0 := zero_smul ℝ _
    rw [hzero] at hline
    exact hline
  have hU₀ :
      cmp98UbarAmbientDeviationMatrix
          (trivialPhysicalGaugeBackground d (M * N') Nc) b x 0 =
        cmp98UbarDeviationCurve
          (trivialPhysicalGaugeBackground d (M * N') Nc) A b x 0 := by
    have hline :=
      cmp98UbarAmbientDeviationMatrix_line_eq_deviationCurve
        (trivialPhysicalGaugeBackground d (M * N') Nc) A b x 0
    have hzero : (0 : ℝ) • physicalSuTangentToAmbient
        (physicalCochainToSuMatrixTangent A) = 0 := zero_smul ℝ _
    rw [hzero] at hline
    exact hline
  rw [hU, hU₀]
  unfold cmp98UbarDeviationCurve
  simpa only [sub_sub_sub_cancel_right] using
    norm_cmp98UbarFourFactorProduct_zero_sub_trivial_le_sourceScale
      U ε hε hsmall A b x hx

/-- The first variation of the literal four-contour deviation is
background-Lipschitz with the explicit quadratic source-length cost.

Here `A` is an unrestricted tangent direction.  In particular, this theorem
must not be specialized using the CMP116 cutoff threshold `ε₁ / gₖ`, which
controls a different field. -/
theorem norm_cmp98UbarDeviationFirstVariation_zero_sub_trivial_le_sourceScale
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hsmall : PhysicalWilsonSmallBackground U ε)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N') (x : FinBox d (M * N'))
    (hx : x ∈ blockOf M N' b.1) :
    ‖cmp98UbarDeviationFirstVariation U A b x 0 -
        cmp98UbarDeviationFirstVariation
          (trivialPhysicalGaugeBackground d (M * N') Nc) A b x 0‖ ≤
      ((2 * (d + 1) * M : ℕ) : ℝ) ^ 2 * ε *
        cmp98SourceFieldSupNorm A := by
  rw [cmp98UbarDeviationFirstVariation_zero_eq_sourceContour,
    cmp98UbarDeviationFirstVariation_zero_eq_sourceContour]
  have hraw :=
    norm_cmp98ContourFirstVariation_zero_sub_trivial_le
      U ε hε hsmall A (cmp98SourceFourContourEdges (Nc := Nc) b x)
  have hlen :
      ((cmp98SourceFourContourEdges (Nc := Nc) b x).length : ℝ) ≤
        ((2 * (d + 1) * M : ℕ) : ℝ) := by
    exact_mod_cast cmp98SourceFourContourEdges_length_le
      (Nc := Nc) b x hx
  calc
    ‖cmp98ContourFirstVariation U A
          (cmp98SourceFourContourEdges (Nc := Nc) b x) 0 -
        cmp98ContourFirstVariation
          (trivialPhysicalGaugeBackground d (M * N') Nc) A
          (cmp98SourceFourContourEdges (Nc := Nc) b x) 0‖
        ≤ ((cmp98SourceFourContourEdges (Nc := Nc) b x).length : ℝ) ^ 2 *
            ε * cmp98SourceFieldSupNorm A := hraw
    _ ≤ ((2 * (d + 1) * M : ℕ) : ℝ) ^ 2 * ε *
          cmp98SourceFieldSupNorm A := by
      gcongr
      exact cmp98SourceFieldSupNorm_nonneg A

/-- The straight coarse transport changes by at most `M * ε` between the
small background and the trivial one. -/
theorem norm_cmp98SourceCoarseContour_zero_sub_trivial_le
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hsmall : PhysicalWilsonSmallBackground U ε)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N') :
    ‖cmp98ContourMatrixCurve U A
          (cmp98SourceCoarseBondPath (Nc := Nc) b) 0 -
        cmp98ContourMatrixCurve
          (trivialPhysicalGaugeBackground d (M * N') Nc) A
          (cmp98SourceCoarseBondPath (Nc := Nc) b) 0‖ ≤
      (M : ℝ) * ε := by
  simpa only [cmp98SourceCoarseBondPath_length] using
    norm_cmp98ContourMatrixCurve_zero_sub_trivial_le
      U ε hε hsmall A (cmp98SourceCoarseBondPath (Nc := Nc) b)

/-- The first variation of the straight coarse transport has the exact
quadratic path-length cost `M²`. -/
theorem norm_cmp98SourceCoarseContourFirstVariation_zero_sub_trivial_le
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hsmall : PhysicalWilsonSmallBackground U ε)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N') :
    ‖cmp98ContourFirstVariation U A
          (cmp98SourceCoarseBondPath (Nc := Nc) b) 0 -
        cmp98ContourFirstVariation
          (trivialPhysicalGaugeBackground d (M * N') Nc) A
          (cmp98SourceCoarseBondPath (Nc := Nc) b) 0‖ ≤
      (M : ℝ) ^ 2 * ε * cmp98SourceFieldSupNorm A := by
  simpa only [cmp98SourceCoarseBondPath_length] using
    norm_cmp98ContourFirstVariation_zero_sub_trivial_le
      U ε hε hsmall A (cmp98SourceCoarseBondPath (Nc := Nc) b)

end

end YangMills.RG
