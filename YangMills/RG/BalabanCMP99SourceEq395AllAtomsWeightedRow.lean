/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceEq395FirstAtomWeightedRow

/-!
# A common weighted row for every physical CMP99 equation (3.95) atom

The first, global-middle species and the two cell-localized species now have
one common positive rate and one explicit volume-independent amplitude.  This
removes the former `species ≠ first` condition from the public estimate.
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

/-- Common volume-independent amplitude for all three correction species. -/
noncomputable def cmp99Eq395PhysicalRAtomWeightedRowAmplitude
    (M depth : ℕ) (spacing epsilon : ℝ) : ℝ :=
  cmp99Eq395PhysicalFirstAtomWeightedRowAmplitude M depth spacing epsilon +
    cmp99Eq395LocalizedAtomWeightedRowAmplitude M depth spacing epsilon
      (cmp99Eq395FirstAtomDecayRate M depth spacing epsilon)

/-- Increasing a nonnegative weighted-row amplitude preserves the
certificate. -/
theorem finitePiLpTypedWeightedRowKernelBound_mono_amplitude
    {ι κ g : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [NormedAddCommGroup g] [NormedSpace ℝ g]
    {T : FinitePiLpField ι g →L[ℝ] FinitePiLpField κ g}
    {dist : κ → ι → ℕ} {A B rate : ℝ}
    (hT : FinitePiLpTypedWeightedRowKernelBound T dist A rate)
    (hAB : A ≤ B) :
    FinitePiLpTypedWeightedRowKernelBound T dist B rate := by
  refine ⟨hT.1.trans hAB, hT.2.1, ?_⟩
  intro source v
  exact (hT.2.2 source v).trans
    (mul_le_mul_of_nonneg_right hAB (norm_nonneg v))

namespace CMP99SourceDependentOmegaGeometry

set_option maxRecDepth 4000 in
set_option maxHeartbeats 8000000 in
/-- Every physical correction atom in the exhaustive three-species alphabet
of (3.95) has the same volume-independent fixed-rate weighted row. -/
theorem cmp99Eq395PhysicalRAtom_weightedRow
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
      (cmp99Eq395PhysicalRAtomWeightedRowAmplitude M depth spacing epsilon)
      (cmp99Eq395FirstAtomDecayRate M depth spacing epsilon) := by
  let rate := cmp99Eq395FirstAtomDecayRate M depth spacing epsilon
  let Afirst := cmp99Eq395PhysicalFirstAtomWeightedRowAmplitude
    M depth spacing epsilon
  let Alocal := cmp99Eq395LocalizedAtomWeightedRowAmplitude
    M depth spacing epsilon rate
  have hrate : 0 < rate := by
    dsimp [rate, cmp99Eq395FirstAtomDecayRate]
    have := cmp99SourceGeneratedCombesThomasRate_pos
      4 M depth hspacing hsmall
    positivity
  cases species with
  | first =>
      have hfirst := cmp99Eq395PhysicalRAtom_first_weightedRow
        D hpi5 P hM depth hspacing background budget fineSmall hsmall cell
      apply finitePiLpTypedWeightedRowKernelBound_mono_amplitude hfirst
      dsimp [cmp99Eq395PhysicalRAtomWeightedRowAmplitude, Afirst, Alocal]
      exact le_add_of_nonneg_right
        (cmp99Eq395PhysicalRAtom_weightedRow_of_ne_first
          D hpi5 P hM depth hspacing hrate background budget fineSmall hsmall
          cell .second (by decide)).1
  | second =>
      have hlocal := cmp99Eq395PhysicalRAtom_weightedRow_of_ne_first
        D hpi5 P hM depth hspacing hrate background budget fineSmall hsmall
        cell .second (by decide)
      apply finitePiLpTypedWeightedRowKernelBound_mono_amplitude hlocal
      dsimp [cmp99Eq395PhysicalRAtomWeightedRowAmplitude, Afirst, Alocal]
      exact le_add_of_nonneg_left
        (cmp99Eq395PhysicalRAtom_first_weightedRow
          D hpi5 P hM depth hspacing background budget fineSmall hsmall cell).1
  | third =>
      have hlocal := cmp99Eq395PhysicalRAtom_weightedRow_of_ne_first
        D hpi5 P hM depth hspacing hrate background budget fineSmall hsmall
        cell .third (by decide)
      apply finitePiLpTypedWeightedRowKernelBound_mono_amplitude hlocal
      dsimp [cmp99Eq395PhysicalRAtomWeightedRowAmplitude, Afirst, Alocal]
      exact le_add_of_nonneg_left
        (cmp99Eq395PhysicalRAtom_first_weightedRow
          D hpi5 P hM depth hspacing background budget fineSmall hsmall cell).1

end CMP99SourceDependentOmegaGeometry
end
end YangMills.RG
