/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceEq395Neumann
import YangMills.RG.BalabanCMP99PatchedParametrixWalkExpansion

/-!
# The exhaustive ordered-walk expansion of CMP99 equation (3.95)

The correction in (3.95) is a finite sum of exactly three literal species for
every source cell.  This file turns that complete finite sum into an ordered
noncommutative alphabet and expands every Neumann layer into words in that
alphabet.

Unlike the separately formalized list of examples followed by "etc." on
CMP99 pp. 412--415, this alphabet is exhaustive by construction for the
already proved operator `R` in (3.95).  No claim about volume-uniform
branching or contraction is made here; those require the subsequent support
and grouping arguments.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped BigOperators Matrix.Norms.L2Operator RealInnerProductSpace

noncomputable section

universe u v

/-- The three summand species occurring literally in the correction of
CMP99 equation (3.95). -/
inductive CMP99Eq395CorrectionSpecies where
  | first
  | second
  | third
deriving DecidableEq, Fintype

/-- One signed atom of `R = -correction`, indexed by its source cell and its
literal position among the three terms of (3.95). -/
def cmp99Eq395RAtom {Index : Type u} {E : Type v} [Ring E]
    (A : E) (AD chi h C : Index → E)
    (label : Index × CMP99Eq395CorrectionSpecies) : E :=
  match label.2 with
  | .first =>
      -cmp99Eq395FirstTerm A (chi label.1) (h label.1) (C label.1)
  | .second =>
      -cmp99Eq395SecondTerm A (AD label.1) (chi label.1)
        (h label.1) (C label.1)
  | .third =>
      -cmp99Eq395ThirdTerm (AD label.1) (chi label.1)
        (h label.1) (C label.1)

/-- The sum over the three-species alphabet is exactly the full correction
`R` for the complete finite index family. -/
theorem sum_cmp99Eq395RAtom_eq_R
    {Index : Type u} {E : Type v} [Fintype Index] [Ring E]
    (A : E) (AD chi h C : Index → E) :
    (∑ label : Index × CMP99Eq395CorrectionSpecies,
        cmp99Eq395RAtom A AD chi h C label) =
      cmp99Eq395R Finset.univ A AD chi h C := by
  rw [Fintype.sum_prod_type]
  have hspecies (i : Index) :
      (∑ species : CMP99Eq395CorrectionSpecies,
          cmp99Eq395RAtom A AD chi h C (i, species)) =
        -cmp99Eq395FirstTerm A (chi i) (h i) (C i) +
        -cmp99Eq395SecondTerm A (AD i) (chi i) (h i) (C i) +
        -cmp99Eq395ThirdTerm (AD i) (chi i) (h i) (C i) := by
    rw [show (Finset.univ : Finset CMP99Eq395CorrectionSpecies) =
        {.first, .second, .third} by
      ext species
      cases species <;> simp]
    simp [cmp99Eq395RAtom]
    abel
  simp only [cmp99Eq395R, cmp99Eq395Correction]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [hspecies]
  abel

/-- Every homogeneous power of the complete correction is the sum over all
ordered words of the literal three-species alphabet.  Multiplication order is
preserved and no operator factors commute. -/
theorem cmp99Eq395R_pow_eq_sum_ordered_atoms
    {Index : Type u} {E : Type v} [Fintype Index] [Ring E]
    (A : E) (AD chi h C : Index → E) (n : ℕ) :
    (cmp99Eq395R Finset.univ A AD chi h C) ^ n =
      ∑ word : Fin n → (Index × CMP99Eq395CorrectionSpecies),
        cmp99OrderedTupleProduct (cmp99Eq395RAtom A AD chi h C) word := by
  rw [← sum_cmp99Eq395RAtom_eq_R]
  exact sum_pow_eq_sum_cmp99OrderedTupleProduct _ n

variable {M Nc Q j : ℕ} [NeZero M] [NeZero Nc] [NeZero Q]
variable {ScaleSite : Fin (j + 2) → Type v}
variable [∀ r, DecidableEq (ScaleSite r)]
variable {Scaled : CMP99SourceScaledStratification
  (FinBox 4 (2 * Q)) (j + 2) ScaleSite}
variable {dist : FinBox 4 (2 * Q) → FinBox 4 (2 * Q) → ℕ}
variable {gap : Fin (j + 1) → ℕ}

namespace CMP99SourceDependentOmegaGeometry

/-- Literal physical atom of the generated source-family correction. -/
noncomputable def cmp99Eq395PhysicalRAtom
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
    (label : FinBox 4 Q × CMP99Eq395CorrectionSpecies) :
    CMP99Eq395AmbientOperator Q Nc :=
  let A := cmp99Eq395PhysicalGlobalMiddle hM depth hspacing background
    budget fineSmall hsmall
  let h := cmp99Eq395PhysicalSmoothMultiplier (Nc := Nc) P
  let chi := cmp99Eq395PhysicalSourceCharacteristic (Nc := Nc)
  let AD := cmp99Eq395PhysicalMiddle D hpi5 hM depth hspacing background
    budget fineSmall hsmall
  let C := cmp99Eq395PhysicalCovariance D hpi5 hM depth hspacing background
    budget fineSmall hsmall
  cmp99Eq395RAtom A AD chi h C label

/-- The physical correction is exactly the finite sum of all literal source
atoms. -/
theorem sum_cmp99Eq395PhysicalRAtom_eq_correction
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
    (∑ label : FinBox 4 Q × CMP99Eq395CorrectionSpecies,
        cmp99Eq395PhysicalRAtom D hpi5 P hM depth hspacing background budget
          fineSmall hsmall label) =
      cmp99Eq395PhysicalCorrection D hpi5 P hM depth hspacing background
        budget fineSmall hsmall := by
  simpa [cmp99Eq395PhysicalRAtom, cmp99Eq395PhysicalCorrection] using
    (sum_cmp99Eq395RAtom_eq_R
      (cmp99Eq395PhysicalGlobalMiddle hM depth hspacing background budget
        fineSmall hsmall)
      (cmp99Eq395PhysicalMiddle D hpi5 hM depth hspacing background budget
        fineSmall hsmall)
      (cmp99Eq395PhysicalSourceCharacteristic (Nc := Nc))
      (cmp99Eq395PhysicalSmoothMultiplier (Nc := Nc) P)
      (cmp99Eq395PhysicalCovariance D hpi5 hM depth hspacing background budget
        fineSmall hsmall))

/-- Exact source-exhaustive degree-`n` expansion of the physical correction. -/
theorem cmp99Eq395PhysicalCorrection_pow_eq_sum_ordered_atoms
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
      spacing epsilon < 1) (n : ℕ) :
    (cmp99Eq395PhysicalCorrection D hpi5 P hM depth hspacing background
      budget fineSmall hsmall) ^ n =
      ∑ word : Fin n → (FinBox 4 Q × CMP99Eq395CorrectionSpecies),
        cmp99OrderedTupleProduct
          (cmp99Eq395PhysicalRAtom D hpi5 P hM depth hspacing background
            budget fineSmall hsmall) word := by
  rw [← sum_cmp99Eq395PhysicalRAtom_eq_correction]
  exact sum_pow_eq_sum_cmp99OrderedTupleProduct _ n

/-- The corrected physical covariance is the countable sum of its complete
finite ordered-word layers.  This equality is algebraic and does not yet
assert the volume-uniform contraction of those layers. -/
theorem cmp99Eq395PhysicalCorrectedCovariance_eq_tsum_ordered_atom_layers
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
    cmp99Eq395PhysicalCorrectedCovariance D hpi5 P hM depth hspacing
        background budget fineSmall hsmall =
      (cmp99Eq395PhysicalPatchedCovariance D hpi5 P hM depth hspacing
        background budget fineSmall hsmall).comp
        (∑' n : ℕ,
          ∑ word : Fin n → (FinBox 4 Q × CMP99Eq395CorrectionSpecies),
            cmp99OrderedTupleProduct
              (cmp99Eq395PhysicalRAtom D hpi5 P hM depth hspacing background
                budget fineSmall hsmall) word) := by
  rw [cmp99Eq395PhysicalCorrectedCovariance_eq_tsum_pow]
  congr 1
  apply tsum_congr
  intro n
  exact cmp99Eq395PhysicalCorrection_pow_eq_sum_ordered_atoms D hpi5 P hM
    depth hspacing background budget fineSmall hsmall n

end CMP99SourceDependentOmegaGeometry

end

end YangMills.RG
