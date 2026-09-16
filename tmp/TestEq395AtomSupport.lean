import YangMills.RG.BalabanCMP99SourceEq395WalkExpansion
import YangMills.RG.BalabanCMP99SourceEq395HeadSupport

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

theorem test_atom_zero_source
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
    (cell : FinBox 4 Q) (species : CMP99Eq395CorrectionSpecies)
    (source target : FinBox 4 (2 * Q)) (v : SUNLieCoord Nc)
    (houtside : ¬ cmp95SourcePeriodicCoarseCellSupport Q cell source) :
    cmp99Eq395PhysicalRAtom D hpi5 P hM depth hspacing background budget
      fineSmall hsmall (cell, species) (singleFinitePiLp source v) target = 0 := by
  have hzero :
      (cmp95SourcePeriodicCoarseSquarePartition P Q).value cell source = 0 :=
    cmp95SourcePeriodicCoarseSquarePartition_value_eq_zero_of_not_support
      P Q cell source houtside
  have hsingle : singleFinitePiLp source (0 : SUNLieCoord Nc) = 0 := by
    apply PiLp.ext
    intro x
    by_cases hx : x = source
    · subst x; simp
    · rw [singleFinitePiLp_of_ne (0 : SUNLieCoord Nc) hx]; rfl
  cases species <;>
    simp [cmp99Eq395PhysicalRAtom, cmp99Eq395RAtom,
      cmp99Eq395FirstTerm, cmp99Eq395SecondTerm, cmp99Eq395ThirdTerm,
      cmp99Eq395PhysicalSmoothMultiplier, finitePiLpScalarMultiplier_single,
      hzero, hsingle]

end CMP99SourceDependentOmegaGeometry
end
end YangMills.RG
