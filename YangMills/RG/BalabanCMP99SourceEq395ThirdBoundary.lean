/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceEq395GroupedCell

/-!
# Boundary support of the third CMP99 equation (3.95) mechanism

The grouped source identity isolates the third mechanism as the commutator
`[chi_Pi A_Pi, h_Pi]`.  On the literal coarse sampling, `h_Pi` equals the
base-cell characteristic.  Consequently the one-site kernel vanishes unless
source and target lie on opposite sides of the physical boundary of `Pi`.

This file records only that exact support statement.  It does not attach an
exponential estimate or rename the still-open regional boundary decay.
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

/-- On the literal coarse lattice the periodized smooth cutoff is exactly
one throughout its owning two-block source cell.  The square normalization
and uniqueness of physical base-cell ownership make the proof insensitive
to degeneracies of small periodic tori. -/
theorem cmp99Eq395SampledCutoff_value_eq_one_of_mem_baseCell
    (P : CMP95SourceSmoothPartitionProfile) {Q : ℕ} [NeZero Q]
    (cell : FinBox 4 Q) (block : FinBox 4 (2 * Q))
    (hblock : block ∈ cmp99SourceBaseCell cell) :
    (cmp95SourcePeriodicCoarseSquarePartition P Q).value cell block = 1 := by
  classical
  let S := cmp95SourcePeriodicCoarseSquarePartition P Q
  have hsingle :
      (∑ other : FinBox 4 Q, (S.value other block) ^ 2) =
        (S.value cell block) ^ 2 := by
    apply Fintype.sum_eq_single cell
    intro other hne
    have houtside :
        ¬cmp95SourcePeriodicCoarseCellSupport Q other block := by
      intro hsupport
      have hother : block ∈ cmp99SourceBaseCell other :=
        cmp95SourcePeriodicCoarseCellSupport_mem_sourceBaseCell
          other block hsupport
      exact hne (cmp99SourceBaseCell_unique hother hblock)
    rw [show S.value other block = 0 by
      exact cmp95SourcePeriodicCoarseSquarePartition_value_eq_zero_of_not_support
        P Q other block houtside]
    norm_num
  have hsquare : (S.value cell block) ^ 2 = 1 := by
    rw [← hsingle]
    exact S.square_sum block
  have hnonneg : 0 ≤ S.value cell block := Real.sqrt_nonneg _
  nlinarith

/-- The CMP95 cutoff sampled in (3.95) is exactly the characteristic of its
physical source cell.  This statement is deliberately kept in the terminal
(3.95) layer so it does not invalidate the generic partition library. -/
theorem cmp99Eq395SampledCutoff_value_eq_piCharacteristic
    (P : CMP95SourceSmoothPartitionProfile) {Q : ℕ} [NeZero Q]
    (cell : FinBox 4 Q) (block : FinBox 4 (2 * Q)) :
    (cmp95SourcePeriodicCoarseSquarePartition P Q).value cell block =
      cmp99SourcePiCharacteristic cell block := by
  classical
  by_cases hblock : block ∈ cmp99SourceBaseCell cell
  · rw [cmp99Eq395SampledCutoff_value_eq_one_of_mem_baseCell
      P cell block hblock]
    simp [cmp99SourcePiCharacteristic, cmp99SourceTildePiLargeBlocks_zero,
      hblock]
  · have houtside :
        ¬cmp95SourcePeriodicCoarseCellSupport Q cell block := by
      intro hsupport
      exact hblock
        (cmp95SourcePeriodicCoarseCellSupport_mem_sourceBaseCell
          cell block hsupport)
    rw [cmp95SourcePeriodicCoarseSquarePartition_value_eq_zero_of_not_support
      P Q cell block houtside]
    simp [cmp99SourcePiCharacteristic, cmp99SourceTildePiLargeBlocks_zero,
      hblock]

/-- The sampled source multiplier is an exact projection on the ambient
coarse field.  This is the operator-level form needed to expose the true
localized parametrix error in the grouped (3.95) atom. -/
theorem cmp99Eq395PhysicalSmoothMultiplier_sq_eq_self
    (P : CMP95SourceSmoothPartitionProfile) (cell : FinBox 4 Q) :
    cmp99Eq395PhysicalSmoothMultiplier (Nc := Nc) P cell *
        cmp99Eq395PhysicalSmoothMultiplier (Nc := Nc) P cell =
      cmp99Eq395PhysicalSmoothMultiplier (Nc := Nc) P cell := by
  change (finitePiLpScalarMultiplier (g := SUNLieCoord Nc)
      (fun block : FinBox 4 (2 * Q) =>
        (cmp95SourcePeriodicCoarseSquarePartition P Q).value cell block)).comp
      (finitePiLpScalarMultiplier (g := SUNLieCoord Nc)
        (fun block : FinBox 4 (2 * Q) =>
          (cmp95SourcePeriodicCoarseSquarePartition P Q).value cell block)) = _
  apply finitePiLpScalarMultiplier_comp_eq_of_pointwise_mul
  intro block
  rw [cmp99Eq395SampledCutoff_value_eq_piCharacteristic]
  simp [cmp99SourcePiCharacteristic]

/-- At the coarse sites on which (3.95) acts, the nominally smooth source
multiplier is literally the source-cell characteristic. -/
theorem cmp99Eq395PhysicalSmoothMultiplier_eq_sourceCharacteristic
    (P : CMP95SourceSmoothPartitionProfile) (cell : FinBox 4 Q) :
    cmp99Eq395PhysicalSmoothMultiplier (Nc := Nc) P cell =
      cmp99Eq395PhysicalSourceCharacteristic (Nc := Nc) cell := by
  apply ContinuousLinearMap.ext
  intro f
  apply PiLp.ext
  intro block
  simp [cmp99Eq395PhysicalSmoothMultiplier,
    cmp99Eq395PhysicalSourceCharacteristic, finitePiLpScalarMultiplier_apply,
    cmp99Eq395SampledCutoff_value_eq_piCharacteristic]

namespace CMP99SourceDependentOmegaGeometry

/-- The grouped left defect is exactly the global--regional middle mismatch
localized by the physical source projection.  No separate commutator term
remains after the literal coarse sampling is used. -/
theorem cmp99Eq395PhysicalGroupedLeftDefect_eq_global_sub_regional
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
    (cell : FinBox 4 Q) :
    let A := cmp99Eq395PhysicalGlobalMiddle hM depth hspacing background
      budget fineSmall hsmall
    let h := cmp99Eq395PhysicalSmoothMultiplier (Nc := Nc) P cell
    let AD := cmp99Eq395PhysicalMiddle D hpi5 hM depth hspacing background
      budget fineSmall hsmall cell
    cmp99Eq395PhysicalGroupedLeftDefect D hpi5 P hM depth hspacing
        background budget fineSmall hsmall cell =
      A * h - h * AD := by
  unfold cmp99Eq395PhysicalGroupedLeftDefect
  dsimp only
  rw [← cmp99Eq395PhysicalSmoothMultiplier_eq_sourceCharacteristic P cell]
  rw [← mul_assoc, cmp99Eq395PhysicalSmoothMultiplier_sq_eq_self]

/-- Exact geometric splitting of the global--regional gluing gap.  The first
term is the part of the global middle which escapes the physical source
cell; the second compares the global and regional middles after the output
has been projected back into that cell.  No decay estimate is hidden in
either summand. -/
theorem cmp99Eq395PhysicalGroupedLeftDefect_eq_escape_add_interiorMismatch
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
    (cell : FinBox 4 Q) :
    let A := cmp99Eq395PhysicalGlobalMiddle hM depth hspacing background
      budget fineSmall hsmall
    let h := cmp99Eq395PhysicalSmoothMultiplier (Nc := Nc) P cell
    let AD := cmp99Eq395PhysicalMiddle D hpi5 hM depth hspacing background
      budget fineSmall hsmall cell
    cmp99Eq395PhysicalGroupedLeftDefect D hpi5 P hM depth hspacing
        background budget fineSmall hsmall cell =
      (1 - h) * (A * h) + h * (A * h - AD) := by
  rw [cmp99Eq395PhysicalGroupedLeftDefect_eq_global_sub_regional]
  dsimp only
  rw [sub_mul, one_mul, mul_sub]
  abel

/-- Resolvent-facing splitting of the same gluing gap.  The first summand is
the global--regional middle difference localized on the input; the second is
the literal regional commutator with the source cutoff.  These are exactly
the two analytic estimates required after the fine cutoff scale is fixed. -/
theorem cmp99Eq395PhysicalGroupedLeftDefect_eq_middleGap_add_commutator
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
    (cell : FinBox 4 Q) :
    let A := cmp99Eq395PhysicalGlobalMiddle hM depth hspacing background
      budget fineSmall hsmall
    let h := cmp99Eq395PhysicalSmoothMultiplier (Nc := Nc) P cell
    let AD := cmp99Eq395PhysicalMiddle D hpi5 hM depth hspacing background
      budget fineSmall hsmall cell
    cmp99Eq395PhysicalGroupedLeftDefect D hpi5 P hM depth hspacing
        background budget fineSmall hsmall cell =
      (A - AD) * h + (AD * h - h * AD) := by
  rw [cmp99Eq395PhysicalGroupedLeftDefect_eq_global_sub_regional]
  dsimp only
  rw [sub_mul]
  abel

/-- Point-source kernel of the global--regional gluing gap.  The global
middle is selected by source membership, whereas the regional middle is
selected by target membership.  This exposes the three genuine geometric
cases without replacing any of them by a bound. -/
theorem cmp99Eq395PhysicalGroupedLeftDefect_single_apply
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
    (cell : FinBox 4 Q) (source target : FinBox 4 (2 * Q))
    (v : SUNLieCoord Nc) :
    let A := cmp99Eq395PhysicalGlobalMiddle hM depth hspacing background
      budget fineSmall hsmall
    let AD := cmp99Eq395PhysicalMiddle D hpi5 hM depth hspacing background
      budget fineSmall hsmall cell
    cmp99Eq395PhysicalGroupedLeftDefect D hpi5 P hM depth hspacing
        background budget fineSmall hsmall cell
          (singleFinitePiLp source v) target =
      cmp99SourcePiCharacteristic cell source •
          A (singleFinitePiLp source v) target -
        cmp99SourcePiCharacteristic cell target •
          AD (singleFinitePiLp source v) target := by
  rw [cmp99Eq395PhysicalGroupedLeftDefect_eq_global_sub_regional]
  dsimp only
  let A := cmp99Eq395PhysicalGlobalMiddle hM depth hspacing background
    budget fineSmall hsmall
  let AD := cmp99Eq395PhysicalMiddle D hpi5 hM depth hspacing background
    budget fineSmall hsmall cell
  let h := cmp99Eq395PhysicalSmoothMultiplier (Nc := Nc) P cell
  change (A (h (singleFinitePiLp source v))) target -
      (h (AD (singleFinitePiLp source v))) target = _
  simp [A, AD, h, cmp99Eq395PhysicalSourceCharacteristic,
    cmp99Eq395PhysicalSmoothMultiplier_eq_sourceCharacteristic,
    finitePiLpScalarMultiplier_apply, finitePiLpScalarMultiplier_single]
  have hsingle : singleFinitePiLp source
        (cmp99SourcePiCharacteristic cell source • v) =
      cmp99SourcePiCharacteristic cell source •
        singleFinitePiLp source v := by
    apply PiLp.ext
    intro block
    by_cases hblock : block = source
    · subst block
      simp
    · simp [singleFinitePiLp_of_ne, hblock]
  rw [hsingle, map_smul, PiLp.smul_apply]

/-- Membership-normalized kernel formula.  Inside--inside is the literal
middle difference, each crossing case contains exactly one propagator, and
outside--outside is zero by simplification of the two displayed `if`s. -/
theorem cmp99Eq395PhysicalGroupedLeftDefect_single_apply_ite
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
    (cell : FinBox 4 Q) (source target : FinBox 4 (2 * Q))
    (v : SUNLieCoord Nc) :
    let A := cmp99Eq395PhysicalGlobalMiddle hM depth hspacing background
      budget fineSmall hsmall
    let AD := cmp99Eq395PhysicalMiddle D hpi5 hM depth hspacing background
      budget fineSmall hsmall cell
    cmp99Eq395PhysicalGroupedLeftDefect D hpi5 P hM depth hspacing
        background budget fineSmall hsmall cell
          (singleFinitePiLp source v) target =
      (if source ∈ cmp99SourceBaseCell cell then
          A (singleFinitePiLp source v) target else 0) -
        (if target ∈ cmp99SourceBaseCell cell then
          AD (singleFinitePiLp source v) target else 0) := by
  rw [cmp99Eq395PhysicalGroupedLeftDefect_single_apply]
  simp [cmp99SourcePiCharacteristic, cmp99SourceTildePiLargeBlocks_zero]

/-- After coarse sampling, the complete grouped correction is the literal
localized parametrix error `h - A (h C h)`.  The first term is a projection,
not merely the square of an abstract smooth multiplier. -/
theorem cmp99Eq395PhysicalGroupedRAtom_eq_cutoff_sub_global_head
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
    (cell : FinBox 4 Q) :
    let h := cmp99Eq395PhysicalSmoothMultiplier (Nc := Nc) P cell
    let A := cmp99Eq395PhysicalGlobalMiddle hM depth hspacing background
      budget fineSmall hsmall
    let C := cmp99Eq395PhysicalCovariance D hpi5 hM depth hspacing background
      budget fineSmall hsmall cell
    cmp99Eq395PhysicalGroupedRAtom D hpi5 P hM depth hspacing background
        budget fineSmall hsmall cell =
      h - A * (h * C * h) := by
  rw [cmp99Eq395PhysicalGroupedRAtom_eq_square_sub_global_head D hpi5 P hM
    depth hspacing background budget fineSmall hsmall cell]
  rw [cmp99Eq395PhysicalSmoothMultiplier_sq_eq_self]

/-- Final global--regional factorization of the grouped (3.95) correction:
the middle mismatch is followed by the literal regional covariance tail. -/
theorem cmp99Eq395PhysicalGroupedRAtom_eq_neg_global_regional_gap_comp_tail
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
    (cell : FinBox 4 Q) :
    let A := cmp99Eq395PhysicalGlobalMiddle hM depth hspacing background
      budget fineSmall hsmall
    let h := cmp99Eq395PhysicalSmoothMultiplier (Nc := Nc) P cell
    let AD := cmp99Eq395PhysicalMiddle D hpi5 hM depth hspacing background
      budget fineSmall hsmall cell
    let C := cmp99Eq395PhysicalCovariance D hpi5 hM depth hspacing background
      budget fineSmall hsmall cell
    cmp99Eq395PhysicalGroupedRAtom D hpi5 P hM depth hspacing background
        budget fineSmall hsmall cell =
      -(A * h - h * AD) * C * h := by
  rw [cmp99Eq395PhysicalGroupedRAtom_eq_neg_defect_comp_tail D hpi5 P hM
    depth hspacing background budget fineSmall hsmall cell]
  rw [cmp99Eq395PhysicalGroupedLeftDefect_eq_global_sub_regional]

/-- Complete two-mechanism factorization of the grouped (3.95) atom.  The
middle comparison and the smooth-cutoff commutator remain separate all the
way to the regional covariance tail, so neither estimate can be replaced by
the other in the final Schur budget. -/
theorem cmp99Eq395PhysicalGroupedRAtom_eq_neg_middleGap_commutator_comp_tail
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
    (cell : FinBox 4 Q) :
    let A := cmp99Eq395PhysicalGlobalMiddle hM depth hspacing background
      budget fineSmall hsmall
    let h := cmp99Eq395PhysicalSmoothMultiplier (Nc := Nc) P cell
    let AD := cmp99Eq395PhysicalMiddle D hpi5 hM depth hspacing background
      budget fineSmall hsmall cell
    let C := cmp99Eq395PhysicalCovariance D hpi5 hM depth hspacing background
      budget fineSmall hsmall cell
    cmp99Eq395PhysicalGroupedRAtom D hpi5 P hM depth hspacing background
        budget fineSmall hsmall cell =
      -((A - AD) * h + (AD * h - h * AD)) * C * h := by
  rw [cmp99Eq395PhysicalGroupedRAtom_eq_neg_global_regional_gap_comp_tail]
  dsimp only
  congr 2
  rw [sub_mul]
  abel

/-- Boundary support of the third mechanism: it vanishes whenever source
and target lie on the same side of the physical source-cell boundary. -/
theorem cmp99Eq395PhysicalThirdLeft_single_apply_eq_zero_of_same_side
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
    (cell : FinBox 4 Q) (source target : FinBox 4 (2 * Q))
    (v : SUNLieCoord Nc)
    (hsame : source ∈ cmp99SourceBaseCell cell ↔
      target ∈ cmp99SourceBaseCell cell) :
    cmp99Eq395PhysicalThirdLeft D hpi5 P hM depth hspacing background
        budget fineSmall hsmall cell (singleFinitePiLp source v) target = 0 := by
  have hchi : cmp99SourcePiCharacteristic cell source =
      cmp99SourcePiCharacteristic cell target := by
    by_cases hsource : source ∈ cmp99SourceBaseCell cell
    · have htarget := hsame.mp hsource
      simp [cmp99SourcePiCharacteristic, cmp99SourceTildePiLargeBlocks_zero,
        hsource, htarget]
    · have htarget : target ∉ cmp99SourceBaseCell cell := by
        intro ht
        exact hsource (hsame.mpr ht)
      simp [cmp99SourcePiCharacteristic, cmp99SourceTildePiLargeBlocks_zero,
        hsource, htarget]
  rw [cmp99Eq395PhysicalThirdLeft_eq_operatorScalarCommutator]
  rw [finitePiLpOperatorScalarCommutator_single_apply,
    cmp99Eq395SampledCutoff_value_eq_piCharacteristic,
    cmp99Eq395SampledCutoff_value_eq_piCharacteristic, hchi, sub_self,
    zero_smul]

end CMP99SourceDependentOmegaGeometry

end

end YangMills.RG
