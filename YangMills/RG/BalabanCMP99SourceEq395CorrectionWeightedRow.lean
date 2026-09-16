/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceEq395AllAtomsWeightedRow

/-!
# Volume-independent weighted row of the full CMP99 equation (3.95) correction

On a point source, exact source support reduces the ambient sum to at most
three labels.  Combining this branching theorem with the common atom bound
gives a weighted-row estimate for the literal full correction, with no factor
depending on the number of source cells.
-/

namespace YangMills.RG
open YangMills Matrix
open scoped BigOperators Matrix.Norms.L2Operator RealInnerProductSpace
noncomputable section

universe v
variable {M Nc Q j : ℕ} [NeZero M] [NeZero Nc] [NeZero Q]
variable {ScaleSite : Fin (j + 2) → Type v}
variable [∀ r, DecidableEq (ScaleSite r)]
variable {Scaled : CMP99SourceScaledStratification
  (FinBox 4 (2 * Q)) (j + 2) ScaleSite}
variable {dist : FinBox 4 (2 * Q) → FinBox 4 (2 * Q) → ℕ}
variable {gap : Fin (j + 1) → ℕ}

/-- Explicit common amplitude of the complete correction: the branching
constant is the literal three-species source alphabet. -/
noncomputable def cmp99Eq395PhysicalCorrectionWeightedRowAmplitude
    (M depth : ℕ) (spacing epsilon : ℝ) : ℝ :=
  3 * cmp99Eq395PhysicalRAtomWeightedRowAmplitude M depth spacing epsilon

namespace CMP99SourceDependentOmegaGeometry

set_option maxRecDepth 4000 in
set_option maxHeartbeats 8000000 in
/-- The complete physical correction in (3.95) has a volume-independent
fixed-rate weighted row. -/
theorem cmp99Eq395PhysicalCorrection_weightedRow
    (D : (cell : FinBox 4 Q) → CMP99SourceDependentOmegaGeometry
      (FinBox 4 (2 * Q)) j ScaleSite Scaled
      (cmp99SourceTildePiLargeBlocks cell 3)
      (cmp99SourceTildePiLargeBlocks cell 4) dist gap)
    (hpi5 : ∀ cell, (D cell).fineRegion (cmp99OmegaZeroIndex j) ⊆
      cmp99SourceTildePiLargeBlocks cell 5)
    (P : CMP95SourceSmoothPartitionProfile)
    (hM : 2 ≤ M) (depth : ℕ) {spacing epsilon : ℝ}
    (hspacing : 0 < spacing)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 M Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff 4 M (depth + 1)
      spacing epsilon < 1) :
    FinitePiLpTypedWeightedRowKernelBound
      (cmp99Eq395PhysicalCorrection D hpi5 P hM depth hspacing background
        budget fineSmall hsmall : CMP99Eq395AmbientOperator Q Nc)
      (finBoxDist : FinBox 4 (2 * Q) → FinBox 4 (2 * Q) → ℕ)
      (cmp99Eq395PhysicalCorrectionWeightedRowAmplitude
        M depth spacing epsilon)
      (cmp99Eq395FirstAtomDecayRate M depth spacing epsilon) := by
  classical
  let A := cmp99Eq395PhysicalRAtomWeightedRowAmplitude
    M depth spacing epsilon
  let rate := cmp99Eq395FirstAtomDecayRate M depth spacing epsilon
  have hatom : ∀ label : FinBox 4 Q × CMP99Eq395CorrectionSpecies,
      FinitePiLpTypedWeightedRowKernelBound
        (cmp99Eq395PhysicalRAtom D hpi5 P hM depth hspacing background budget
          fineSmall hsmall label : CMP99Eq395AmbientOperator Q Nc)
        (finBoxDist : FinBox 4 (2 * Q) → FinBox 4 (2 * Q) → ℕ)
        A rate := by
    intro label
    exact cmp99Eq395PhysicalRAtom_weightedRow D hpi5 P hM depth hspacing
      background budget fineSmall hsmall label.1 label.2
  have hA : 0 ≤ A := (hatom
    (default, CMP99Eq395CorrectionSpecies.first)).1
  refine ⟨mul_nonneg (by norm_num) hA, (hatom
    (default, CMP99Eq395CorrectionSpecies.first)).2.1, ?_⟩
  intro source v
  let relevant := cmp99Eq395SourceRelevantLabels source
  have hcard : relevant.card ≤ 3 := by
    simpa [relevant] using card_cmp99Eq395SourceRelevantLabels_le_three source
  simp_rw [cmp99Eq395PhysicalCorrection_apply_single_eq_sum_relevant
    D hpi5 P hM depth hspacing background budget fineSmall hsmall]
  calc
    ∑ target : FinBox 4 (2 * Q),
          Real.exp (rate * (finBoxDist target source : ℝ)) *
            ‖∑ label ∈ relevant,
              cmp99Eq395PhysicalRAtom D hpi5 P hM depth hspacing background
                budget fineSmall hsmall label
                (singleFinitePiLp source v) target‖
        ≤ ∑ target : FinBox 4 (2 * Q),
            ∑ label ∈ relevant,
              Real.exp (rate * (finBoxDist target source : ℝ)) *
                ‖cmp99Eq395PhysicalRAtom D hpi5 P hM depth hspacing
                  background budget fineSmall hsmall label
                  (singleFinitePiLp source v) target‖ := by
          apply Finset.sum_le_sum
          intro target _
          calc
            Real.exp (rate * (finBoxDist target source : ℝ)) *
                ‖∑ label ∈ relevant,
                  cmp99Eq395PhysicalRAtom D hpi5 P hM depth hspacing
                    background budget fineSmall hsmall label
                    (singleFinitePiLp source v) target‖
              ≤ Real.exp (rate * (finBoxDist target source : ℝ)) *
                  ∑ label ∈ relevant,
                    ‖cmp99Eq395PhysicalRAtom D hpi5 P hM depth hspacing
                      background budget fineSmall hsmall label
                      (singleFinitePiLp source v) target‖ :=
                mul_le_mul_of_nonneg_left (norm_sum_le _ _)
                  (Real.exp_pos _).le
            _ = ∑ label ∈ relevant,
                Real.exp (rate * (finBoxDist target source : ℝ)) *
                  ‖cmp99Eq395PhysicalRAtom D hpi5 P hM depth hspacing
                    background budget fineSmall hsmall label
                    (singleFinitePiLp source v) target‖ := by
              rw [Finset.mul_sum]
    _ = ∑ label ∈ relevant,
          ∑ target : FinBox 4 (2 * Q),
            Real.exp (rate * (finBoxDist target source : ℝ)) *
              ‖cmp99Eq395PhysicalRAtom D hpi5 P hM depth hspacing background
                budget fineSmall hsmall label
                (singleFinitePiLp source v) target‖ := by
          rw [Finset.sum_comm]
    _ ≤ ∑ _label ∈ relevant, A * ‖v‖ := by
          apply Finset.sum_le_sum
          intro label _
          exact (hatom label).2.2 source v
    _ = (relevant.card : ℝ) * (A * ‖v‖) := by
          simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 3 * (A * ‖v‖) := by
          gcongr
          exact_mod_cast hcard
    _ = (3 * A) * ‖v‖ := by ring

end CMP99SourceDependentOmegaGeometry
end
end YangMills.RG

