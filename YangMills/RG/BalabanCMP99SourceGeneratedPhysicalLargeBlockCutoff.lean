/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceGeneratedPhysicalCutoffWeighted
import YangMills.RG.BalabanCMP99SourceRegionalLargeBlockSlope

/-!
# PRE-VALIDATION: source large-block cutoff on the generated physical precision

The source of this module is present, but its `.olean` has not yet been
materialized and the result has not yet been verified by the Lean compiler.

This specializes the already sealed fixed-output commutator estimate to the
single physical `CMP95SourceSmoothPartitionProfile`.  The carrier equality is
used explicitly, and the certified slope times the generated precision range
is rewritten to the literal `4 * derivBound / M` gain.  The Laplacian and
normalized `Q'^* Q'` budgets remain separate until their final addition.

This file does not identify an ambient precision with a regional compression,
compose with a Dirichlet Green operator, or claim `‖R'‖ < 1`.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator RealInnerProductSpace

noncomputable section

variable {M Q Nc : ℕ}
variable [NeZero M] [NeZero Q] [NeZero Nc]

/-- The literal source large-block cutoff, transported to a site of the
generated physical precision through the exact carrier equality. -/
noncomputable def cmp99SourceGeneratedPhysicalLargeBlockCutoff
    (P : CMP95SourceSmoothPartitionProfile)
    (Omega : ActiveGaugeRegion 4 (2 * (M * Q))) (depth : ℕ)
    (cell : FinBox 4 Q)
    (x : ActiveGaugeRegion.Site
      (cmp99IteratedLiftActiveRegion (M := M) Omega (depth + 1))) : ℝ :=
  let hsize := cmp99RegionalLatticeSize_sourceLargeBlockCarrier M Q depth
  (cmp99SourceRegionalLargeBlockSquarePartition
    (M := M) (Q := Q) (depth := depth) P).value cell (hsize ▸ x.1)

/-- The transported physical cutoff has exactly the source large-block
Lipschitz constant; no auxiliary terminal-scale profile is substituted. -/
theorem norm_cmp99SourceGeneratedPhysicalLargeBlockCutoff_sub_le
    (P : CMP95SourceSmoothPartitionProfile)
    (Omega : ActiveGaugeRegion 4 (2 * (M * Q))) (depth : ℕ)
    (cell : FinBox 4 Q)
    (target source : ActiveGaugeRegion.Site
      (cmp99IteratedLiftActiveRegion (M := M) Omega (depth + 1))) :
    ‖cmp99SourceGeneratedPhysicalLargeBlockCutoff P Omega depth cell target -
        cmp99SourceGeneratedPhysicalLargeBlockCutoff P Omega depth cell source‖ ≤
      ((8 * P.derivBound) /
        cmp99SourceRegionalLargeBlockCutoffScale M depth) *
        (finBoxDist target.1 source.1 : ℝ) := by
  let hsize := cmp99RegionalLatticeSize_sourceLargeBlockCarrier M Q depth
  have h :=
    norm_cmp99SourceRegionalLargeBlockSquarePartition_value_sub_le
      (M := M) (Q := Q) (depth := depth) P cell
      (hsize ▸ source.1) (hsize ▸ target.1)
  have hdist : finBoxDist (hsize ▸ source.1) (hsize ▸ target.1) =
      finBoxDist source.1 target.1 :=
    finBoxDist_cast_size hsize source.1 target.1
  simpa [cmp99SourceGeneratedPhysicalLargeBlockCutoff, hsize, hdist,
    finBoxDist_comm] using h

/-- Covariant-Laplacian contribution after the exact source-scale
`slope * range = 4 * derivBound / M` cancellation. -/
noncomputable def cmp99SourceGeneratedPhysicalLargeBlockLaplacianBudget
    (P : CMP95SourceSmoothPartitionProfile)
    (M : ℕ) (spacing rate : ℝ) : ℝ :=
  ((4 * P.derivBound) / (M : ℝ)) *
    cmp99ActiveRegionSourceCovariantLaplacianWeightedRowAmplitude
      4 spacing rate

/-- Normalized `Q'^* Q'` contribution after the same exact source-scale
cancellation. -/
noncomputable def cmp99SourceGeneratedPhysicalLargeBlockMassBudget
    (P : CMP95SourceSmoothPartitionProfile)
    (M depth : ℕ) (spacing epsilon rate : ℝ) : ℝ :=
  ((4 * P.derivBound) / (M : ℝ)) *
    (|cmp99SourceGeneratedPhysicalMass 4 M (depth + 1) spacing epsilon| *
      (Real.exp (rate * ((M ^ (depth + 1) - 1 : ℕ) : ℝ)) *
        (cmp99SourceBlockAverageWeight M 4) ^ (depth + 1)))

/-- Literal sum of the two source-scale physical commutator budgets. -/
noncomputable def cmp99SourceGeneratedPhysicalLargeBlockCutoffBudget
    (P : CMP95SourceSmoothPartitionProfile)
    (M depth : ℕ) (spacing epsilon rate : ℝ) : ℝ :=
  cmp99SourceGeneratedPhysicalLargeBlockLaplacianBudget P M spacing rate +
    cmp99SourceGeneratedPhysicalLargeBlockMassBudget
      P M depth spacing epsilon rate

/-- Fixed-output weighted estimate for the literal generated precision and
the literal source large-block cutoff. -/
theorem
    cmp99SourceGeneratedPhysicalPrecision_largeBlockCutoff_fixedOutputWeighted
    (P : CMP95SourceSmoothPartitionProfile) (hM : 2 ≤ M)
    (Omega : ActiveGaugeRegion 4 (2 * (M * Q))) (depth : ℕ)
    {spacing epsilon rate : ℝ} (hspacing : 0 < spacing) (hrate : 0 ≤ rate)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize M (2 * (M * Q)) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 M Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize M (2 * (M * Q)) (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (cell : FinBox 4 Q) :
    FinitePiLpTypedFixedOutputWeightedKernelBound
      (finitePiLpScalarCommutator
        (ι := ActiveGaugeRegion.Site
          (cmp99IteratedLiftActiveRegion (M := M) Omega (depth + 1)))
        (g := SUNLieCoord Nc)
        (cmp99SourceGeneratedPhysicalLargeBlockCutoff P Omega depth cell)
        (cmp99SourceGeneratedPhysicalPrecision (by norm_num) hM Omega depth
          spacing epsilon background budget fineSmall))
      (fun (target source : ActiveGaugeRegion.Site
          (cmp99IteratedLiftActiveRegion (M := M) Omega (depth + 1))) =>
        finBoxDist target.1 source.1)
      (cmp99SourceGeneratedPhysicalLargeBlockCutoffBudget
        P M depth spacing epsilon rate) rate := by
  let slope : ℝ := (8 * P.derivBound) /
    cmp99SourceRegionalLargeBlockCutoffScale M depth
  have hslope : 0 ≤ slope := by
    dsimp [slope]
    positivity
  have h :=
    cmp99SourceGeneratedPhysicalPrecision_cutoffCommutator_fixedOutputWeighted
      (d := 4) (M := M) (N := 2 * (M * Q)) (Nc := Nc)
      (by norm_num) hM Omega depth hspacing hrate hslope background budget
      fineSmall
      (cmp99SourceGeneratedPhysicalLargeBlockCutoff P Omega depth cell)
      (norm_cmp99SourceGeneratedPhysicalLargeBlockCutoff_sub_le
        P Omega depth cell)
  simpa [slope, cmp99SourceGeneratedPhysicalCutoffCommutatorBudget,
    cmp99SourceGeneratedPhysicalLaplacianCutoffBudget,
    cmp99SourceGeneratedPhysicalMassCutoffBudget,
    cmp99SourceGeneratedPhysicalLargeBlockCutoffBudget,
    cmp99SourceGeneratedPhysicalLargeBlockLaplacianBudget,
    cmp99SourceGeneratedPhysicalLargeBlockMassBudget,
    cmp99SourceRegionalLargeBlockSlope_mul_precisionRange] using h

/-- Pointwise exponential form of the same source-scale physical estimate. -/
theorem
    cmp99SourceGeneratedPhysicalPrecision_largeBlockCutoff_exponentialKernelBound
    (P : CMP95SourceSmoothPartitionProfile) (hM : 2 ≤ M)
    (Omega : ActiveGaugeRegion 4 (2 * (M * Q))) (depth : ℕ)
    {spacing epsilon rate : ℝ} (hspacing : 0 < spacing) (hrate : 0 < rate)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize M (2 * (M * Q)) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 M Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize M (2 * (M * Q)) (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (cell : FinBox 4 Q) :
    FinitePiLpTypedExponentialKernelBound
      (finitePiLpScalarCommutator
        (ι := ActiveGaugeRegion.Site
          (cmp99IteratedLiftActiveRegion (M := M) Omega (depth + 1)))
        (g := SUNLieCoord Nc)
        (cmp99SourceGeneratedPhysicalLargeBlockCutoff P Omega depth cell)
        (cmp99SourceGeneratedPhysicalPrecision (by norm_num) hM Omega depth
          spacing epsilon background budget fineSmall))
      (fun (target source : ActiveGaugeRegion.Site
          (cmp99IteratedLiftActiveRegion (M := M) Omega (depth + 1))) =>
        finBoxDist target.1 source.1)
      (cmp99SourceGeneratedPhysicalLargeBlockCutoffBudget
        P M depth spacing epsilon rate) rate := by
  apply finitePiLpTypedExponentialKernelBound_of_fixedOutputWeighted _ _ hrate
  exact
    cmp99SourceGeneratedPhysicalPrecision_largeBlockCutoff_fixedOutputWeighted
      P hM Omega depth hspacing hrate.le background budget fineSmall cell

end

end YangMills.RG
