/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP102PhysicalRightVariationLinearity

/-!
# Two-field estimate for the complete physical CMP102 correction

The nonlinear logarithmic coordinate is already controlled in two fields,
and the subtracted right variation is now proved exactly linear.  Their
difference therefore gives a source-faithful estimate for the complete
CMP98 (122) remainder.

The only term not yet reduced to the field sup norm is the norm of the
literal physical right variation evaluated at `A - B`; it is retained
verbatim rather than replaced by an abstract Lipschitz premise.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {d M N' Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero N'] [NeZero Nc]

/-- Explicit current two-field budget for the complete correction.  The
remaining linear term is the literal physical right variation. -/
def cmp102SourceCorrectionTwoFieldBudget
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A B : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N') (t r s : ℝ) : ℝ :=
  nearLogDerivativeBudget s *
      cmp102SourceRelativeDeviationTwoFieldBudget A B t r +
    |t| * ‖cmp98Eq119NonlinearRightVariation U (A - B) b‖

set_option maxHeartbeats 10000000 in
/-- The complete literal CMP98 (122) remainder is controlled in two fields.
No correction-level Lipschitz constant is supplied. -/
theorem norm_cmp98Eq122NonlinearLogRemainder_twoField_sub_le
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A B : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N') (t r s : ℝ)
    (hbase : ∀ x ∈ blockOf M N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix U b x 0‖ ≤ 1 / 3)
    (hA : |t| * cmp98SourceFieldSupNorm A ≤ 1 / 2)
    (hB : |t| * cmp98SourceFieldSupNorm B ≤ 1 / 2)
    (hrA : 1 / 3 + cmp98SourceContourDisplacementBudget A t ≤ r)
    (hrB : 1 / 3 + cmp98SourceContourDisplacementBudget B t ≤ r)
    (hr1 : r < 1)
    (hsA : cmp98SourcePhysicalBlockDisplacementBudget A t r ≤ s)
    (hsB : cmp98SourcePhysicalBlockDisplacementBudget B t r ≤ s)
    (hs1 : s < 1) :
    ‖cmp98Eq122NonlinearLogRemainder U A b t -
        cmp98Eq122NonlinearLogRemainder U B b t‖ ≤
      cmp102SourceCorrectionTwoFieldBudget U A B b t r s := by
  let LA := cmp98Eq119NonlinearLogCoordinate U A b t
  let LB := cmp98Eq119NonlinearLogCoordinate U B b t
  let VA := cmp98Eq119NonlinearRightVariation U A b
  let VB := cmp98Eq119NonlinearRightVariation U B b
  let V := cmp98Eq119NonlinearRightVariation U (A - B) b
  have hlog : ‖LA - LB‖ ≤
      nearLogDerivativeBudget s *
        cmp102SourceRelativeDeviationTwoFieldBudget A B t r := by
    simpa [LA, LB] using
      norm_cmp98Eq119NonlinearLogCoordinate_twoField_sub_le
        U A B b t r s hbase hA hB hrA hrB hr1 hsA hsB hs1
  have hsmall : ∀ x ∈ blockOf M N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix U b x 0‖ < 1 := by
    intro x hx
    exact (hbase x hx).trans_lt (by norm_num)
  have hvariation : V = VA - VB := by
    exact cmp98Eq119NonlinearRightVariation_sub U A B b hsmall
  have halg :
      (LA - t • VA) - (LB - t • VB) =
        (LA - LB) - t • V := by
    rw [hvariation]
    module
  unfold cmp98Eq122NonlinearLogRemainder
  change ‖(LA - t • VA) - (LB - t • VB)‖ ≤ _
  rw [halg]
  unfold cmp102SourceCorrectionTwoFieldBudget
  calc
    ‖(LA - LB) - t • V‖ ≤ ‖LA - LB‖ + ‖t • V‖ :=
      norm_sub_le _ _
    _ ≤ nearLogDerivativeBudget s *
          cmp102SourceRelativeDeviationTwoFieldBudget A B t r +
        ‖t • V‖ :=
      add_le_add hlog le_rfl
    _ = nearLogDerivativeBudget s *
          cmp102SourceRelativeDeviationTwoFieldBudget A B t r +
        |t| * ‖V‖ := by
      congr 1
      change ‖(t : ℂ) • V‖ = _
      rw [norm_smul]
      simp only [Complex.norm_real, Real.norm_eq_abs]

end

end YangMills.RG
