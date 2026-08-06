/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP95SourceSmoothPartitionSecondDerivative

/-!
# PRE-VALIDATION: second differences of the CMP95 source profile

The source is present, but this module's `.olean` has not yet been materialized
and its declarations have not yet been verified by the Lean compiler.

CMP96 (2.40) multiplies a discrete cutoff Laplacian by the value component of
the regional Green estimate.  The latter has quadratic physical scale, so the
cutoff coefficient must be estimated at inverse-square cutoff scale before the
two are composed.  This module supplies the one-dimensional analytic core:
the canonical second-derivative budget derived from the printed smooth compact
support controls the centred second difference quadratically.

No periodic cutoff is identified here.  In particular, these lemmas do not
apply automatically to the existing square-root periodization; that physical
dictionary remains a separate obligation.
-/

namespace YangMills.RG

noncomputable section

namespace CMP95SourceSmoothPartitionProfile

/-- The derivative of the selected profile is globally Lipschitz with the
canonical second-derivative budget. -/
theorem norm_deriv_sub_deriv_le_secondDerivBound
    (P : CMP95SourceSmoothPartitionProfile) (x y : ℝ) :
    ‖deriv P.value y - deriv P.value x‖ ≤
      P.secondDerivBound * ‖y - x‖ := by
  have hdiff : Differentiable ℝ (deriv P.value) :=
    (P.contDiff.of_le (by simp)).differentiable_deriv_two
  apply convex_univ.norm_image_sub_le_of_norm_deriv_le
      (s := Set.univ) (f := deriv P.value)
      (fun t _ht => hdiff t) (fun t _ht => ?_)
      (Set.mem_univ x) (Set.mem_univ y)
  simpa [show (2 : ℕ) = 1 + 1 by omega, iteratedDeriv_succ] using
    P.norm_iteratedDeriv_two_le_secondDerivBound t

/-- First-order Taylor remainder obtained only from the globally Lipschitz
derivative.  The intentionally non-sharp constant avoids introducing a
separate Taylor coefficient into the physical budget. -/
theorem norm_value_sub_firstOrder_le_secondDerivBound
    (P : CMP95SourceSmoothPartitionProfile) (x y : ℝ) :
    ‖P.value y - P.value x - (y - x) * deriv P.value x‖ ≤
      P.secondDerivBound * ‖y - x‖ ^ 2 := by
  let φ : ℝ →L[ℝ] ℝ :=
    ContinuousLinearMap.toSpanSingleton ℝ (deriv P.value x)
  have hbound : ∀ z ∈ segment ℝ x y,
      ‖fderiv ℝ P.value z - φ‖ ≤
        (P.secondDerivBound * ‖y - x‖) := by
    intro z hz
    have hzx : ‖z - x‖ ≤ ‖y - x‖ :=
      norm_sub_le_of_mem_segment hz
    calc
      ‖fderiv ℝ P.value z - φ‖ =
          ‖deriv P.value z - deriv P.value x‖ := by
        change ‖fderiv ℝ P.value z -
            ContinuousLinearMap.toSpanSingleton ℝ (deriv P.value x)‖ = _
        rw [← toSpanSingleton_deriv, ← map_sub,
          ContinuousLinearMap.norm_toSpanSingleton]
      _ ≤ P.secondDerivBound * ‖z - x‖ :=
        P.norm_deriv_sub_deriv_le_secondDerivBound x z
      _ ≤ P.secondDerivBound * ‖y - x‖ :=
        mul_le_mul_of_nonneg_left hzx P.secondDerivBound_nonneg
  have h := (convex_segment x y).norm_image_sub_le_of_norm_fderiv_le'
    (f := P.value) (s := segment ℝ x y) (φ := φ)
    (fun z _hz => P.contDiff.differentiable (by simp) z)
    hbound (left_mem_segment ℝ x y) (right_mem_segment ℝ x y)
  simpa [φ, pow_two, mul_assoc] using h

/-- The centred second difference has the quadratic scale required by the
cutoff-Laplacian species. -/
theorem norm_centeredSecondDifference_le_secondDerivBound
    (P : CMP95SourceSmoothPartitionProfile) (x h : ℝ) :
    ‖P.value (x + h) - 2 * P.value x + P.value (x - h)‖ ≤
      (2 * P.secondDerivBound) * ‖h‖ ^ 2 := by
  have hplus :=
    P.norm_value_sub_firstOrder_le_secondDerivBound x (x + h)
  have hminus :=
    P.norm_value_sub_firstOrder_le_secondDerivBound x (x - h)
  calc
    ‖P.value (x + h) - 2 * P.value x + P.value (x - h)‖ =
        ‖(P.value (x + h) - P.value x -
              ((x + h) - x) * deriv P.value x) +
          (P.value (x - h) - P.value x -
              ((x - h) - x) * deriv P.value x)‖ := by
        congr 1
        ring
    _ ≤
        ‖P.value (x + h) - P.value x -
            ((x + h) - x) * deriv P.value x‖ +
          ‖P.value (x - h) - P.value x -
            ((x - h) - x) * deriv P.value x‖ := norm_add_le _ _
    _ ≤ P.secondDerivBound * ‖(x + h) - x‖ ^ 2 +
          P.secondDerivBound * ‖(x - h) - x‖ ^ 2 :=
      add_le_add hplus hminus
    _ = (2 * P.secondDerivBound) * ‖h‖ ^ 2 := by
      rw [show (x + h) - x = h by ring,
        show (x - h) - x = -h by ring, norm_neg]
      ring

end CMP95SourceSmoothPartitionProfile

end

end YangMills.RG
