/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceEq395CorrectionWeightedRow

/-!
# Species-sharp weighted row for the CMP99 equation (3.95) correction

The common-amplitude estimate charges every active species for both the
global-middle and localized costs.  A point source has at most one active
label of each of the three literal species.  Keeping those species separate
therefore replaces `3 * (A_first + A_local)` by the source-faithful
`A_first + 2 * A_local`, still without an ambient-volume factor.
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

/-- The literal weighted-row cost of one correction species. -/
noncomputable def cmp99Eq395PhysicalSpeciesWeightedRowAmplitude
    (M depth : ℕ) (spacing epsilon : ℝ) :
    CMP99Eq395CorrectionSpecies → ℝ
  | .first =>
      cmp99Eq395PhysicalFirstAtomWeightedRowAmplitude M depth spacing epsilon
  | .second | .third =>
      cmp99Eq395LocalizedAtomWeightedRowAmplitude M depth spacing epsilon
        (cmp99Eq395FirstAtomDecayRate M depth spacing epsilon)

/-- Species-sharp amplitude of the complete correction. -/
noncomputable def cmp99Eq395PhysicalCorrectionSharpWeightedRowAmplitude
    (M depth : ℕ) (spacing epsilon : ℝ) : ℝ :=
  cmp99Eq395PhysicalFirstAtomWeightedRowAmplitude M depth spacing epsilon +
    2 * cmp99Eq395LocalizedAtomWeightedRowAmplitude M depth spacing epsilon
      (cmp99Eq395FirstAtomDecayRate M depth spacing epsilon)

namespace CMP99SourceDependentOmegaGeometry

set_option maxRecDepth 4000
set_option maxHeartbeats 8000000

/-- Each atom carries only the cost of its own literal species. -/
theorem cmp99Eq395PhysicalRAtom_species_weightedRow
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
      spacing epsilon < 1)
    (cell : FinBox 4 Q) (species : CMP99Eq395CorrectionSpecies) :
    FinitePiLpTypedWeightedRowKernelBound
      (cmp99Eq395PhysicalRAtom D hpi5 P hM depth hspacing background budget
        fineSmall hsmall (cell, species) : CMP99Eq395AmbientOperator Q Nc)
      (finBoxDist : FinBox 4 (2 * Q) → FinBox 4 (2 * Q) → ℕ)
      (cmp99Eq395PhysicalSpeciesWeightedRowAmplitude
        M depth spacing epsilon species)
      (cmp99Eq395FirstAtomDecayRate M depth spacing epsilon) := by
  cases species with
  | first =>
      exact cmp99Eq395PhysicalRAtom_first_weightedRow D hpi5 P hM depth
        hspacing background budget fineSmall hsmall cell
  | second =>
      exact cmp99Eq395PhysicalRAtom_weightedRow_of_ne_first D hpi5 P hM
        depth hspacing (by
          dsimp [cmp99Eq395FirstAtomDecayRate]
          have := cmp99SourceGeneratedCombesThomasRate_pos
            4 M depth hspacing hsmall
          positivity) background budget fineSmall hsmall cell .second (by decide)
  | third =>
      exact cmp99Eq395PhysicalRAtom_weightedRow_of_ne_first D hpi5 P hM
        depth hspacing (by
          dsimp [cmp99Eq395FirstAtomDecayRate]
          have := cmp99SourceGeneratedCombesThomasRate_pos
            4 M depth hspacing hsmall
          positivity) background budget fineSmall hsmall cell .third (by decide)

/-- The full correction has the exact one-global-plus-two-local source
branching cost. -/
theorem cmp99Eq395PhysicalCorrection_sharp_weightedRow
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
      (cmp99Eq395PhysicalCorrectionSharpWeightedRowAmplitude
        M depth spacing epsilon)
      (cmp99Eq395FirstAtomDecayRate M depth spacing epsilon) := by
  classical
  let amp := cmp99Eq395PhysicalSpeciesWeightedRowAmplitude
    M depth spacing epsilon
  let rate := cmp99Eq395FirstAtomDecayRate M depth spacing epsilon
  have hatom : ∀ label : FinBox 4 Q × CMP99Eq395CorrectionSpecies,
      FinitePiLpTypedWeightedRowKernelBound
        (cmp99Eq395PhysicalRAtom D hpi5 P hM depth hspacing background budget
          fineSmall hsmall label : CMP99Eq395AmbientOperator Q Nc)
        (finBoxDist : FinBox 4 (2 * Q) → FinBox 4 (2 * Q) → ℕ)
        (amp label.2) rate := by
    intro label
    exact cmp99Eq395PhysicalRAtom_species_weightedRow D hpi5 P hM depth
      hspacing background budget fineSmall hsmall label.1 label.2
  have hamp_nonneg : ∀ species, 0 ≤ amp species := by
    intro species
    exact (hatom (default, species)).1
  have htotal_nonneg :
      0 ≤ cmp99Eq395PhysicalCorrectionSharpWeightedRowAmplitude
        M depth spacing epsilon := by
    dsimp [cmp99Eq395PhysicalCorrectionSharpWeightedRowAmplitude, amp,
      cmp99Eq395PhysicalSpeciesWeightedRowAmplitude]
    have hfirst := hamp_nonneg CMP99Eq395CorrectionSpecies.first
    have hlocal := hamp_nonneg CMP99Eq395CorrectionSpecies.second
    positivity
  refine ⟨htotal_nonneg, (hatom
    (default, CMP99Eq395CorrectionSpecies.first)).2.1, ?_⟩
  intro source v
  let relevant := cmp99Eq395SourceRelevantLabels source
  let ownerFiber : Finset (FinBox 4 Q × CMP99Eq395CorrectionSpecies) :=
    {cmp99SourceBaseCellOwner source} ×ˢ Finset.univ
  have hsubset : relevant ⊆ ownerFiber := by
    intro label hlabel
    rw [Finset.mem_product]
    exact ⟨by
      simpa [relevant] using
        fst_eq_sourceBaseCellOwner_of_mem_cmp99Eq395SourceRelevantLabels
          source label hlabel, Finset.mem_univ _⟩
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
    _ ≤ ∑ label ∈ relevant, amp label.2 * ‖v‖ := by
          apply Finset.sum_le_sum
          intro label _
          exact (hatom label).2.2 source v
    _ ≤ ∑ label ∈ ownerFiber, amp label.2 * ‖v‖ :=
          Finset.sum_le_sum_of_subset_of_nonneg hsubset (by
            intro label _ _
            exact mul_nonneg (hamp_nonneg label.2) (norm_nonneg v))
    _ = cmp99Eq395PhysicalCorrectionSharpWeightedRowAmplitude
          M depth spacing epsilon * ‖v‖ := by
          simp [ownerFiber, amp, cmp99Eq395PhysicalSpeciesWeightedRowAmplitude,
            cmp99Eq395PhysicalCorrectionSharpWeightedRowAmplitude]
          rw [show (Finset.univ : Finset CMP99Eq395CorrectionSpecies) =
            {.first, .second, .third} by
              ext species
              cases species <;> simp]
          simp
          ring

end CMP99SourceDependentOmegaGeometry
end
end YangMills.RG
