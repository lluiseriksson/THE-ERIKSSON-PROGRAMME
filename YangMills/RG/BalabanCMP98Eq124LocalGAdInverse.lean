/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP98Eq124ContourSplit
import YangMills.RG.BalabanCMP98NearLogGAdInverse

/-!
# Literal local `g(ad)⁻¹` factors in CMP98 equation (124)

The Mercator derivatives in the physical block average are now rewritten
point by point as the certified inverse operators printed in (124).  This
module performs that substitution both for the middle contour and for the
sum of the other three ordered contour variations.

The latter sum is deliberately not claimed to be the final three printed
correction lines: their source-specific algebraic regrouping remains a
separate step.  What is closed here is the analytic dictionary producing
each local `g(ad y_x)⁻¹` from the literal four-contour holonomy.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {d M N' Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero N'] [NeZero Nc]

local instance cmp98Eq124LocalInvMatrixL2NormOneClass :
    NormOneClass (Matrix (Fin Nc) (Fin Nc) ℂ) where
  norm_one := by
    rw [← Matrix.diagonal_one, Matrix.l2_opNorm_diagonal]
    simp

/-- The middle-contour contribution after the literal local `g(ad)⁻¹`
substitution. -/
def cmp98Eq124MiddleGAdInvVariation
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N') : Matrix (Fin Nc) (Fin Nc) ℂ :=
  ((M : ℝ) ^ d)⁻¹ •
    ∑ x ∈ blockOf M N' b.1,
      let Y := cmp98UbarAmbientDeviationMatrix U b x 0
      cmp98GAdInv (nearLog Y)
        (NormedSpace.exp (-(nearLog Y)) *
          cmp98UbarMiddleContourVariation U A b x 0)

/-- The three raw non-middle contour contributions after the same literal
local `g(ad)⁻¹` substitution. -/
def cmp98Eq124CorrectionGAdInvVariation
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N') : Matrix (Fin Nc) (Fin Nc) ℂ :=
  ((M : ℝ) ^ d)⁻¹ •
    ∑ x ∈ blockOf M N' b.1,
      let Y := cmp98UbarAmbientDeviationMatrix U b x 0
      cmp98GAdInv (nearLog Y)
        (NormedSpace.exp (-(nearLog Y)) *
          cmp98UbarThreeContourCorrections U A b x 0)

/-- Every local middle-contour Mercator derivative is exactly its printed
`g(ad y_x)⁻¹` form. -/
theorem cmp98Eq124_localMiddleLogVariation_eq_gadInv
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N') (x : FinBox d (M * N'))
    (hsmall : ‖cmp98UbarAmbientDeviationMatrix U b x 0‖ < 1)
    (hg : Real.exp
      (2 * ‖nearLog (cmp98UbarAmbientDeviationMatrix U b x 0)‖) < 2) :
    (∑' n : ℕ, nearLogTermFDeriv
        (cmp98UbarAmbientDeviationMatrix U b x 0) n)
        (cmp98UbarMiddleContourVariation U A b x 0) =
      cmp98GAdInv
        (nearLog (cmp98UbarAmbientDeviationMatrix U b x 0))
        (NormedSpace.exp
            (-(nearLog (cmp98UbarAmbientDeviationMatrix U b x 0))) *
          cmp98UbarMiddleContourVariation U A b x 0) :=
  nearLog_fderiv_apply_eq_cmp98GAdInv hsmall hg _

/-- Every local sum of the other three contour variations has the analogous
exact `g(ad y_x)⁻¹` representation. -/
theorem cmp98Eq124_localCorrectionLogVariation_eq_gadInv
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N') (x : FinBox d (M * N'))
    (hsmall : ‖cmp98UbarAmbientDeviationMatrix U b x 0‖ < 1)
    (hg : Real.exp
      (2 * ‖nearLog (cmp98UbarAmbientDeviationMatrix U b x 0)‖) < 2) :
    (∑' n : ℕ, nearLogTermFDeriv
        (cmp98UbarAmbientDeviationMatrix U b x 0) n)
        (cmp98UbarThreeContourCorrections U A b x 0) =
      cmp98GAdInv
        (nearLog (cmp98UbarAmbientDeviationMatrix U b x 0))
        (NormedSpace.exp
            (-(nearLog (cmp98UbarAmbientDeviationMatrix U b x 0))) *
          cmp98UbarThreeContourCorrections U A b x 0) :=
  nearLog_fderiv_apply_eq_cmp98GAdInv hsmall hg _

/-- The complete block-averaged middle term is literally the average of the
certified local inverse expressions. -/
theorem cmp98Eq124MiddleLogVariation_eq_gadInv
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N')
    (hsmall : ∀ x ∈ blockOf M N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix U b x 0‖ < 1)
    (hg : ∀ x ∈ blockOf M N' b.1,
      Real.exp
        (2 * ‖nearLog (cmp98UbarAmbientDeviationMatrix U b x 0)‖) < 2) :
    cmp98Eq124MiddleLogVariation U A b =
      cmp98Eq124MiddleGAdInvVariation U A b := by
  unfold cmp98Eq124MiddleLogVariation cmp98Eq124MiddleGAdInvVariation
  apply congrArg (((M : ℝ) ^ d)⁻¹ • ·)
  apply Finset.sum_congr rfl
  intro x hx
  exact cmp98Eq124_localMiddleLogVariation_eq_gadInv U A b x
    (hsmall x hx) (hg x hx)

/-- The complete raw correction term is likewise the average of certified
local inverse expressions. -/
theorem cmp98Eq124CorrectionLogVariation_eq_gadInv
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N')
    (hsmall : ∀ x ∈ blockOf M N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix U b x 0‖ < 1)
    (hg : ∀ x ∈ blockOf M N' b.1,
      Real.exp
        (2 * ‖nearLog (cmp98UbarAmbientDeviationMatrix U b x 0)‖) < 2) :
    cmp98Eq124CorrectionLogVariation U A b =
      cmp98Eq124CorrectionGAdInvVariation U A b := by
  unfold cmp98Eq124CorrectionLogVariation
    cmp98Eq124CorrectionGAdInvVariation
  apply congrArg (((M : ℝ) ^ d)⁻¹ • ·)
  apply Finset.sum_congr rfl
  intro x hx
  exact cmp98Eq124_localCorrectionLogVariation_eq_gadInv U A b x
    (hsmall x hx) (hg x hx)

/-- Source-faithful local-inverse form of the complete physical logarithmic
variation: the main contour and all remaining ordered contour terms now
carry the actual `g(ad y_x)⁻¹` generated by the local holonomy logarithm. -/
theorem cmp98UbarLogAveragePhysicalVariation_eq_gadInv_middle_add_corrections
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N')
    (hsmall : ∀ x ∈ blockOf M N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix U b x 0‖ < 1)
    (hg : ∀ x ∈ blockOf M N' b.1,
      Real.exp
        (2 * ‖nearLog (cmp98UbarAmbientDeviationMatrix U b x 0)‖) < 2) :
    cmp98UbarLogAveragePhysicalVariation U A b =
      cmp98Eq124MiddleGAdInvVariation U A b +
        cmp98Eq124CorrectionGAdInvVariation U A b := by
  rw [cmp98UbarLogAveragePhysicalVariation_eq_middle_add_corrections,
    cmp98Eq124MiddleLogVariation_eq_gadInv U A b hsmall hg,
    cmp98Eq124CorrectionLogVariation_eq_gadInv U A b hsmall hg]

/-- Source-radius form of the block-averaged middle identity.  The single
geometric deviation bound `≤ 1/3` generates both analytic smallness and the
local `g(ad)⁻¹` contraction. -/
theorem cmp98Eq124MiddleLogVariation_eq_gadInv_of_norm_le_third
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N')
    (hthird : ∀ x ∈ blockOf M N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix U b x 0‖ ≤ 1 / 3) :
    cmp98Eq124MiddleLogVariation U A b =
      cmp98Eq124MiddleGAdInvVariation U A b := by
  unfold cmp98Eq124MiddleLogVariation cmp98Eq124MiddleGAdInvVariation
  apply congrArg (((M : ℝ) ^ d)⁻¹ • ·)
  apply Finset.sum_congr rfl
  intro x hx
  exact nearLog_fderiv_apply_eq_cmp98GAdInv_of_norm_le_third
    (hthird x hx) _

/-- Source-radius form for the sum of the three non-middle contour
variations. -/
theorem cmp98Eq124CorrectionLogVariation_eq_gadInv_of_norm_le_third
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N')
    (hthird : ∀ x ∈ blockOf M N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix U b x 0‖ ≤ 1 / 3) :
    cmp98Eq124CorrectionLogVariation U A b =
      cmp98Eq124CorrectionGAdInvVariation U A b := by
  unfold cmp98Eq124CorrectionLogVariation
    cmp98Eq124CorrectionGAdInvVariation
  apply congrArg (((M : ℝ) ^ d)⁻¹ • ·)
  apply Finset.sum_congr rfl
  intro x hx
  exact nearLog_fderiv_apply_eq_cmp98GAdInv_of_norm_le_third
    (hthird x hx) _

/-- **Physical source-radius endpoint for CMP98 (124).**  The complete
logarithmic variation carries the certified pointwise `g(ad y_x)⁻¹`
operators under only the literal holonomy-deviation bound `≤ 1/3`; no
independent inverse or exponential-smallness certificate remains. -/
theorem cmp98UbarLogAveragePhysicalVariation_eq_gadInv_of_norm_le_third
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N')
    (hthird : ∀ x ∈ blockOf M N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix U b x 0‖ ≤ 1 / 3) :
    cmp98UbarLogAveragePhysicalVariation U A b =
      cmp98Eq124MiddleGAdInvVariation U A b +
        cmp98Eq124CorrectionGAdInvVariation U A b := by
  rw [cmp98UbarLogAveragePhysicalVariation_eq_middle_add_corrections,
    cmp98Eq124MiddleLogVariation_eq_gadInv_of_norm_le_third U A b hthird,
    cmp98Eq124CorrectionLogVariation_eq_gadInv_of_norm_le_third U A b hthird]

end

end YangMills.RG
