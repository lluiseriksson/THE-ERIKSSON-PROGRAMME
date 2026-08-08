/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceEq395GroupedRAtomDecay
import YangMills.RG.BalabanCMP99SourceEq395Neumann
import YangMills.RG.FinitePiLpScalarCommutator

/-!
# Volume-independent decay and contraction of the grouped CMP99 correction

For a point source the complete correction is exactly the grouped atom of
the unique physical source-cell owner.  The grouped atom estimate therefore
passes to the complete correction without summing over cells or species.
The resulting kernel bound is converted into an explicit Schur contraction
and consumed by the exact corrected-covariance inverse theorem.
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

namespace CMP99SourceDependentOmegaGeometry

/-- Explicit Schur amplitude obtained directly from the grouped physical
atom.  It contains no volume cardinality and no sum over correction species. -/
noncomputable def cmp99Eq395PhysicalGroupedCorrectionSchurAmplitude
    (M depth : ℕ) (spacing epsilon : ℝ) : ℝ :=
  cmp99Eq395PhysicalGroupedRAtomDecayAmplitude M depth spacing epsilon *
    cmp99OmegaSiteExpSumBound
      (cmp99Eq395PhysicalGroupedRAtomDecayRate M depth spacing epsilon)

set_option maxRecDepth 5000 in
set_option maxHeartbeats 2000000 in
/-- The complete physical correction inherits the fixed-rate kernel bound of
one grouped atom.  Uniqueness of the source-cell owner prevents any branching
or volume factor. -/
theorem cmp99Eq395PhysicalCorrection_grouped_exponentialKernelBound
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
    let R : CMP99Eq395AmbientOperator Q Nc :=
      cmp99Eq395PhysicalCorrection D hpi5 P hM depth hspacing background
        budget fineSmall hsmall
    FinitePiLpTypedExponentialKernelBound R
      (finBoxDist : FinBox 4 (2 * Q) → FinBox 4 (2 * Q) → ℕ)
      (cmp99Eq395PhysicalGroupedRAtomDecayAmplitude
        M depth spacing epsilon)
      (cmp99Eq395PhysicalGroupedRAtomDecayRate
        M depth spacing epsilon) := by
  dsimp only
  let owner : FinBox 4 Q := cmp99SourceBaseCellOwner
    (default : FinBox 4 (2 * Q))
  have hbase := cmp99Eq395PhysicalGroupedRAtom_exponentialKernelBound
    D hpi5 P hM depth hspacing background budget fineSmall hsmall owner
  refine ⟨hbase.1, hbase.2.1, ?_⟩
  intro source target v
  rw [cmp99Eq395PhysicalCorrection_apply_single_eq_grouped_owner
    D hpi5 P hM depth hspacing background budget fineSmall hsmall]
  exact (cmp99Eq395PhysicalGroupedRAtom_exponentialKernelBound
    D hpi5 P hM depth hspacing background budget fineSmall hsmall
      (cmp99SourceBaseCellOwner source)).2.2 source target v

set_option maxRecDepth 5000 in
set_option maxHeartbeats 3000000 in
set_option synthInstance.maxHeartbeats 200000 in
/-- The grouped correction has a volume-independent operator-norm bound with
the explicit grouped Schur amplitude. -/
theorem norm_cmp99Eq395PhysicalCorrection_le_groupedSchurAmplitude
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
    ‖cmp99Eq395PhysicalCorrection D hpi5 P hM depth hspacing background
      budget fineSmall hsmall‖ ≤
      cmp99Eq395PhysicalGroupedCorrectionSchurAmplitude
        M depth spacing epsilon := by
  let R := cmp99Eq395PhysicalCorrection D hpi5 P hM depth hspacing
    background budget fineSmall hsmall
  let A := cmp99Eq395PhysicalGroupedRAtomDecayAmplitude
    M depth spacing epsilon
  let rate := cmp99Eq395PhysicalGroupedRAtomDecayRate
    M depth spacing epsilon
  let S := cmp99OmegaSiteExpSumBound rate
  have hkernel := cmp99Eq395PhysicalCorrection_grouped_exponentialKernelBound
    D hpi5 P hM depth hspacing background budget fineSmall hsmall
  have hrate : 0 < rate := by
    exact hkernel.2.1
  have hS : 0 ≤ S := by
    dsimp [S, cmp99OmegaSiteExpSumBound]
    exact tsum_nonneg fun _ ↦ mul_nonneg (Nat.cast_nonneg _) (Real.exp_pos _).le
  have hsum : ∀ source : FinBox 4 (2 * Q),
      ∑ target : FinBox 4 (2 * Q),
        Real.exp (-(rate * (finBoxDist source target : ℝ))) ≤ S := by
    intro source
    simpa [finBoxDist_comm] using
      (finBoxDist_exp_sum_le_cmp99OmegaSiteExpSumBound
        (Q := Q) source hrate)
  simpa [R, A, rate, S,
    cmp99Eq395PhysicalGroupedCorrectionSchurAmplitude] using
      (finitePiLpOpNorm_le_of_exponentialKernelBound R finBoxDist
        (fun x y ↦ finBoxDist_comm x y) hS hkernel hsum)

set_option maxRecDepth 5000 in
set_option maxHeartbeats 4000000 in
/-- Under the explicit grouped Schur smallness condition, the generated
global middle composed with the corrected physical covariance is exactly the
identity.  No correction-norm or atom estimate remains as an input. -/
theorem cmp99Eq395PhysicalGlobalMiddle_comp_correctedCovariance_eq_id_of_groupedSchurSmall
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
    (hschur : cmp99Eq395PhysicalGroupedCorrectionSchurAmplitude
      M depth spacing epsilon < 1) :
    (cmp99Eq395PhysicalGlobalMiddle hM depth hspacing background budget
      fineSmall hsmall).comp
        (cmp99Eq395PhysicalCorrectedCovariance D hpi5 P hM depth hspacing
          background budget fineSmall hsmall) =
      ContinuousLinearMap.id ℝ
        (GaugeZeroCochain 4 (2 * Q) (SUNLieCoord Nc)) := by
  apply cmp99Eq395PhysicalGlobalMiddle_comp_correctedCovariance_eq_id
  exact (norm_cmp99Eq395PhysicalCorrection_le_groupedSchurAmplitude
    D hpi5 P hM depth hspacing background budget fineSmall hsmall).trans_lt
      hschur

end CMP99SourceDependentOmegaGeometry

end

end YangMills.RG
