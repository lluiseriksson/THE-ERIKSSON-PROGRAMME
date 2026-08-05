/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceGeneratedPhysicalLargeBlockCutoff
import YangMills.RG.BalabanCMP99SourceSeparatedLargeBlockPartition

/-!
# PRE-VALIDATION: separated-scale physical CMP99 cutoff

The source below is present, but its `.olean` has not yet been materialized
and its results have not yet been verified by the Lean compiler.

This is the source-faithful two-parameter specialization of the generated
physical cutoff estimate.  The RG ratio `L` controls the generated precision,
its range and its Poincare/coercivity package.  The independent large-block
parameter `K` controls the regional cell side and leaves the exact gain

`slope * generatedRange = 4 * derivBound / K`.

The covariant-Laplacian and normalized `Q'^* Q'` contributions remain two
separately named budgets and are added only at the final physical endpoint.
No regional Green estimate or contraction is claimed here.  Nor does this
brick discharge the later CMP99 Theorem-3.15 regularity condition coupling
the printed large-block parameter to `alpha_0`; that belongs to the
covariance/source dictionary, not to this direct finite-dimensional
commutator estimate.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator RealInnerProductSpace

noncomputable section

variable {L K Q Nc : ℕ}
variable [NeZero L] [NeZero K] [NeZero Q] [NeZero Nc]

/-- The separated large-block cutoff transported to the site carrier of the
generated physical precision with RG ratio `L`. -/
noncomputable def cmp99SourceSeparatedGeneratedPhysicalLargeBlockCutoff
    (P : CMP95SourceSmoothPartitionProfile)
    (Omega : ActiveGaugeRegion 4 (2 * (K * Q))) (depth : ℕ)
    (cell : FinBox 4 Q)
    (x : ActiveGaugeRegion.Site
      (cmp99IteratedLiftActiveRegion (M := L) Omega (depth + 1))) : ℝ :=
  let hsize :=
    cmp99RegionalLatticeSize_sourceSeparatedLargeBlockCarrier L K Q depth
  (cmp99SourceSeparatedLargeBlockSquarePartition
    (L := L) (K := K) (Q := Q) (depth := depth) P).value cell (hsize ▸ x.1)

/-- The transported cutoff retains the source slope with `L` and `K`
separate. -/
theorem norm_cmp99SourceSeparatedGeneratedPhysicalLargeBlockCutoff_sub_le
    (P : CMP95SourceSmoothPartitionProfile)
    (Omega : ActiveGaugeRegion 4 (2 * (K * Q))) (depth : ℕ)
    (cell : FinBox 4 Q)
    (target source : ActiveGaugeRegion.Site
      (cmp99IteratedLiftActiveRegion (M := L) Omega (depth + 1))) :
    ‖cmp99SourceSeparatedGeneratedPhysicalLargeBlockCutoff
          P Omega depth cell target -
        cmp99SourceSeparatedGeneratedPhysicalLargeBlockCutoff
          P Omega depth cell source‖ ≤
      ((8 * P.derivBound) /
        cmp99SourceSeparatedLargeBlockCutoffScale L K depth) *
        (finBoxDist target.1 source.1 : ℝ) := by
  let hsize :=
    cmp99RegionalLatticeSize_sourceSeparatedLargeBlockCarrier L K Q depth
  change ‖(cmp99SourceSeparatedLargeBlockSquarePartition
          (L := L) (K := K) (Q := Q) (depth := depth) P).value cell
          (hsize ▸ target.1) -
        (cmp99SourceSeparatedLargeBlockSquarePartition
          (L := L) (K := K) (Q := Q) (depth := depth) P).value cell
          (hsize ▸ source.1)‖ ≤ _
  rw [← finBoxDist_cast_size hsize target.1 source.1]
  simpa only [norm_sub_rev] using
    (norm_cmp99SourceSeparatedLargeBlockSquarePartition_value_sub_le
      (L := L) (K := K) (Q := Q) (depth := depth) P cell
      (hsize ▸ target.1) (hsize ▸ source.1))

/-- Covariant-Laplacian contribution after the independent `K^-1`
cancellation. -/
noncomputable def cmp99SourceSeparatedGeneratedPhysicalLargeBlockLaplacianBudget
    (P : CMP95SourceSmoothPartitionProfile)
    (K : ℕ) (spacing rate : ℝ) : ℝ :=
  ((4 * P.derivBound) / (K : ℝ)) *
    cmp99ActiveRegionSourceCovariantLaplacianWeightedRowAmplitude
      4 spacing rate

/-- Normalized `Q'^* Q'` contribution.  Its generated mass, range and row
weight depend on the RG ratio `L`, while the cutoff gain depends on `K`. -/
noncomputable def cmp99SourceSeparatedGeneratedPhysicalLargeBlockMassBudget
    (P : CMP95SourceSmoothPartitionProfile)
    (L K depth : ℕ) (spacing epsilon rate : ℝ) : ℝ :=
  ((4 * P.derivBound) / (K : ℝ)) *
    (|cmp99SourceGeneratedPhysicalMass 4 L (depth + 1) spacing epsilon| *
      (Real.exp (rate * ((L ^ (depth + 1) - 1 : ℕ) : ℝ)) *
        (cmp99SourceBlockAverageWeight L 4) ^ (depth + 1)))

/-- The cutoff numerator after removing the independent large-block factor.
It depends on the RG tower and physical parameters, but not on `K`. -/
noncomputable def cmp99SourceSeparatedGeneratedPhysicalLargeBlockCutoffNumerator
    (P : CMP95SourceSmoothPartitionProfile)
    (L depth : ℕ) (spacing epsilon rate : ℝ) : ℝ :=
  (4 * P.derivBound) *
    (cmp99ActiveRegionSourceCovariantLaplacianWeightedRowAmplitude
        4 spacing rate +
      |cmp99SourceGeneratedPhysicalMass 4 L (depth + 1) spacing epsilon| *
        (Real.exp (rate * ((L ^ (depth + 1) - 1 : ℕ) : ℝ)) *
          (cmp99SourceBlockAverageWeight L 4) ^ (depth + 1)))

/-- Literal sum of the two source-separated physical commutator budgets. -/
noncomputable def cmp99SourceSeparatedGeneratedPhysicalLargeBlockCutoffBudget
    (P : CMP95SourceSmoothPartitionProfile)
    (L K depth : ℕ) (spacing epsilon rate : ℝ) : ℝ :=
  cmp99SourceSeparatedGeneratedPhysicalLargeBlockLaplacianBudget
      P K spacing rate +
    cmp99SourceSeparatedGeneratedPhysicalLargeBlockMassBudget
      P L K depth spacing epsilon rate

/-- The independent source parameter occurs in the cutoff budget only through
the literal factor `K^-1`. -/
theorem cmp99SourceSeparatedGeneratedPhysicalLargeBlockCutoffBudget_eq
    (P : CMP95SourceSmoothPartitionProfile)
    (L K depth : ℕ) (spacing epsilon rate : ℝ) :
    cmp99SourceSeparatedGeneratedPhysicalLargeBlockCutoffBudget
        P L K depth spacing epsilon rate =
      cmp99SourceSeparatedGeneratedPhysicalLargeBlockCutoffNumerator
        P L depth spacing epsilon rate / (K : ℝ) := by
  unfold cmp99SourceSeparatedGeneratedPhysicalLargeBlockCutoffBudget
    cmp99SourceSeparatedGeneratedPhysicalLargeBlockLaplacianBudget
    cmp99SourceSeparatedGeneratedPhysicalLargeBlockMassBudget
    cmp99SourceSeparatedGeneratedPhysicalLargeBlockCutoffNumerator
  ring

/-- For every fixed RG tower and physical background parameters, the
source-separated cutoff budget is below one for some integer large-block
factor `K >= 2`.  This is only cutoff-budget attainment; it does not include
the regional Green, overlap, shell, or Schur factors of window 15. -/
theorem exists_cmp99SourceSeparatedGeneratedPhysicalLargeBlockCutoffBudget_lt_one
    (P : CMP95SourceSmoothPartitionProfile)
    (L depth : ℕ) (spacing epsilon rate : ℝ) :
    ∃ K : ℕ, 2 ≤ K ∧
      cmp99SourceSeparatedGeneratedPhysicalLargeBlockCutoffBudget
        P L K depth spacing epsilon rate < 1 := by
  obtain ⟨n, hn⟩ := exists_nat_gt
    (cmp99SourceSeparatedGeneratedPhysicalLargeBlockCutoffNumerator
      P L depth spacing epsilon rate)
  let K := n + 2
  have hKpos : (0 : ℝ) < (K : ℝ) := by
    exact_mod_cast (by omega : 0 < K)
  have hnumK :
      cmp99SourceSeparatedGeneratedPhysicalLargeBlockCutoffNumerator
          P L depth spacing epsilon rate < (K : ℝ) := by
    dsimp [K]
    push_cast
    linarith
  refine ⟨K, by omega, ?_⟩
  rw [cmp99SourceSeparatedGeneratedPhysicalLargeBlockCutoffBudget_eq]
  exact (div_lt_one hKpos).2 hnumK

/-- On the diagonal `K = L`, the separated budget is definitionally the
previously sealed one-parameter budget. -/
theorem cmp99SourceSeparatedGeneratedPhysicalLargeBlockCutoffBudget_self
    (P : CMP95SourceSmoothPartitionProfile)
    (L depth : ℕ) (spacing epsilon rate : ℝ) :
    cmp99SourceSeparatedGeneratedPhysicalLargeBlockCutoffBudget
        P L L depth spacing epsilon rate =
      cmp99SourceGeneratedPhysicalLargeBlockCutoffBudget
        P L depth spacing epsilon rate := by
  rfl

/-- Fixed-output weighted estimate for the literal generated precision and
the source-separated large-block cutoff. -/
theorem
    cmp99SourceSeparatedGeneratedPhysicalPrecision_largeBlockCutoff_fixedOutputWeighted
    (P : CMP95SourceSmoothPartitionProfile) (hL : 2 ≤ L)
    (Omega : ActiveGaugeRegion 4 (2 * (K * Q))) (depth : ℕ)
    {spacing epsilon rate : ℝ} (hspacing : 0 < spacing) (hrate : 0 ≤ rate)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize L (2 * (K * Q)) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 L Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize L (2 * (K * Q)) (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (cell : FinBox 4 Q) :
    FinitePiLpTypedFixedOutputWeightedKernelBound
      (finitePiLpScalarCommutator
        (ι := ActiveGaugeRegion.Site
          (cmp99IteratedLiftActiveRegion (M := L) Omega (depth + 1)))
        (g := SUNLieCoord Nc)
        (cmp99SourceSeparatedGeneratedPhysicalLargeBlockCutoff
          P Omega depth cell)
        (cmp99SourceGeneratedPhysicalPrecision (by norm_num) hL Omega depth
          spacing epsilon background budget fineSmall))
      (fun (target source : ActiveGaugeRegion.Site
          (cmp99IteratedLiftActiveRegion (M := L) Omega (depth + 1))) =>
        finBoxDist target.1 source.1)
      (cmp99SourceSeparatedGeneratedPhysicalLargeBlockCutoffBudget
        P L K depth spacing epsilon rate) rate := by
  let slope : ℝ := (8 * P.derivBound) /
    cmp99SourceSeparatedLargeBlockCutoffScale L K depth
  have hslope : 0 ≤ slope := by
    dsimp [slope]
    exact div_nonneg
      (mul_nonneg (by norm_num) P.derivBound_nonneg) (Nat.cast_nonneg _)
  have h :=
    cmp99SourceGeneratedPhysicalPrecision_cutoffCommutator_fixedOutputWeighted
      (d := 4) (M := L) (N := 2 * (K * Q)) (Nc := Nc)
      (by norm_num) hL Omega depth hspacing hrate hslope background budget
      fineSmall
      (cmp99SourceSeparatedGeneratedPhysicalLargeBlockCutoff
        P Omega depth cell)
      (norm_cmp99SourceSeparatedGeneratedPhysicalLargeBlockCutoff_sub_le
        P Omega depth cell)
  simpa [slope, cmp99SourceGeneratedPhysicalCutoffCommutatorBudget,
    cmp99SourceGeneratedPhysicalLaplacianCutoffBudget,
    cmp99SourceGeneratedPhysicalMassCutoffBudget,
    cmp99SourceSeparatedGeneratedPhysicalLargeBlockCutoffBudget,
    cmp99SourceSeparatedGeneratedPhysicalLargeBlockLaplacianBudget,
    cmp99SourceSeparatedGeneratedPhysicalLargeBlockMassBudget,
    cmp99SourceSeparatedLargeBlockSlope_mul_precisionRange] using h

/-- Pointwise exponential form of the same source-separated estimate. -/
theorem
    cmp99SourceSeparatedGeneratedPhysicalPrecision_largeBlockCutoff_exponentialKernelBound
    (P : CMP95SourceSmoothPartitionProfile) (hL : 2 ≤ L)
    (Omega : ActiveGaugeRegion 4 (2 * (K * Q))) (depth : ℕ)
    {spacing epsilon rate : ℝ} (hspacing : 0 < spacing) (hrate : 0 < rate)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize L (2 * (K * Q)) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 L Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize L (2 * (K * Q)) (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (cell : FinBox 4 Q) :
    FinitePiLpTypedExponentialKernelBound
      (finitePiLpScalarCommutator
        (ι := ActiveGaugeRegion.Site
          (cmp99IteratedLiftActiveRegion (M := L) Omega (depth + 1)))
        (g := SUNLieCoord Nc)
        (cmp99SourceSeparatedGeneratedPhysicalLargeBlockCutoff
          P Omega depth cell)
        (cmp99SourceGeneratedPhysicalPrecision (by norm_num) hL Omega depth
          spacing epsilon background budget fineSmall))
      (fun (target source : ActiveGaugeRegion.Site
          (cmp99IteratedLiftActiveRegion (M := L) Omega (depth + 1))) =>
        finBoxDist target.1 source.1)
      (cmp99SourceSeparatedGeneratedPhysicalLargeBlockCutoffBudget
        P L K depth spacing epsilon rate) rate := by
  apply finitePiLpTypedExponentialKernelBound_of_fixedOutputWeighted _ _ hrate
  exact
    cmp99SourceSeparatedGeneratedPhysicalPrecision_largeBlockCutoff_fixedOutputWeighted
      P hL Omega depth hspacing hrate.le background budget fineSmall cell

end

end YangMills.RG
