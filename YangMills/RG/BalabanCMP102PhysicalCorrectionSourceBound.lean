/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP102PhysicalRightVariationBound

/-!
# Source-sup-norm bound for the complete CMP102 correction

This module consumes the physical right-variation estimate in the complete
two-field CMP98 (122) remainder.  The resulting public bound contains no norm
of a correction operator: every term is an explicit scalar coefficient times
the physical source-field sup norm.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {d M N' Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero N'] [NeZero Nc]

/-- Explicit Lipschitz coefficient for the logarithmic-coordinate part of
the CMP98 (122) correction. -/
def cmp102SourceLogCorrectionLinearRate
    (d M : ℕ) (r s : ℝ) : ℝ :=
  nearLogDerivativeBudget s *
      ((cmp102ExpLipschitzBudget (cmp98SourceLogAverageRadius r) *
            (nearLogDerivativeBudget r *
              (((2 * (d + 1) * M : ℕ) : ℝ) *
                cmp102ExpLipschitzBudget (1 / 2))) +
          cmp98SourceOuterExpNormBudget r *
            ((M : ℝ) * cmp102ExpLipschitzBudget (1 / 2))) *
        cmp98SourceOuterExpNormBudget r)

/-- Explicit Lipschitz coefficient for the complete CMP98 (122) correction,
after factoring out `|t|` and the physical source-field sup norm. -/
def cmp102SourceCorrectionLinearRate
    (d M : ℕ) (r s : ℝ) : ℝ :=
  cmp102SourceLogCorrectionLinearRate d M r s +
    cmp102SourceRightVariationLinearRate d M r

/-- The previously structured two-field budget is controlled entirely by
the explicit rate and the source-field sup norm of `A - B`. -/
theorem cmp102SourceCorrectionTwoFieldBudget_le_sourceSupNorm
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A B : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N') (t r s : ℝ)
    (hbase : ∀ x ∈ blockOf M N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix U b x 0‖ ≤ 1 / 3)
    (hr13 : 1 / 3 ≤ r) (hr1 : r < 1) :
    cmp102SourceCorrectionTwoFieldBudget U A B b t r s ≤
      |t| * cmp102SourceCorrectionLinearRate d M r s *
        cmp98SourceFieldSupNorm (A - B) := by
  let S := cmp98SourceFieldSupNorm (A - B)
  let V := cmp98Eq119NonlinearRightVariation U (A - B) b
  let L := cmp102SourceLogCorrectionLinearRate d M r s
  let Rv := cmp102SourceRightVariationLinearRate d M r
  have hstructured :
      cmp102SourceCorrectionTwoFieldBudget U A B b t r s =
        |t| * L * S + |t| * ‖V‖ := by
    dsimp only [L, S, V]
    unfold cmp102SourceCorrectionTwoFieldBudget
      cmp102SourceRelativeDeviationTwoFieldBudget
      cmp102SourceNonlinearBlockTwoFieldBudget
      cmp102SourceUbarExpTwoFieldBudget
      cmp102SourceFourContourTwoFieldBudget
      cmp102SourceCoarseContourTwoFieldBudget
      cmp102SourceLogCorrectionLinearRate
    ring
  have hvariation : ‖V‖ ≤ Rv * S := by
    simpa [V, Rv, S] using
      norm_cmp98Eq119NonlinearRightVariation_le_sourceSupNorm
        U (A - B) b r hbase hr13 hr1
  rw [hstructured]
  calc
    |t| * L * S + |t| * ‖V‖
        ≤ |t| * L * S + |t| * (Rv * S) := by
      exact add_le_add (le_refl _) <|
        mul_le_mul_of_nonneg_left hvariation (abs_nonneg t)
    _ = |t| * cmp102SourceCorrectionLinearRate d M r s * S := by
      simp only [cmp102SourceCorrectionLinearRate, L, Rv]
      ring
    _ = |t| * cmp102SourceCorrectionLinearRate d M r s *
          cmp98SourceFieldSupNorm (A - B) := rfl

set_option maxHeartbeats 10000000 in
/-- **Complete physical two-field source bound.**  The literal CMP98 (122)
remainder is Lipschitz in the physical source field with an explicit,
volume-independent coefficient. -/
theorem norm_cmp98Eq122NonlinearLogRemainder_twoField_sub_le_sourceSupNorm
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
      |t| * cmp102SourceCorrectionLinearRate d M r s *
        cmp98SourceFieldSupNorm (A - B) := by
  calc
    ‖cmp98Eq122NonlinearLogRemainder U A b t -
        cmp98Eq122NonlinearLogRemainder U B b t‖
        ≤ cmp102SourceCorrectionTwoFieldBudget U A B b t r s :=
      norm_cmp98Eq122NonlinearLogRemainder_twoField_sub_le
        U A B b t r s hbase hA hB hrA hrB hr1 hsA hsB hs1
    _ ≤ |t| * cmp102SourceCorrectionLinearRate d M r s *
          cmp98SourceFieldSupNorm (A - B) := by
      apply cmp102SourceCorrectionTwoFieldBudget_le_sourceSupNorm
        U A B b t r s hbase
      · exact (le_add_of_nonneg_right
          (cmp98SourceContourDisplacementBudget_nonneg A t)).trans hrA
      · exact hr1

end

end YangMills.RG
