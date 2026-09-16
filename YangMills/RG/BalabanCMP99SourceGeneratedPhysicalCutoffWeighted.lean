/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceGeneratedCombesThomas
import YangMills.RG.BalabanCMP99SourceGeneratedPhysicalPrecisionDirectOutputRow
import YangMills.RG.FinitePiLpScalarCommutator
import YangMills.RG.FinitePiLpTypedScalarCommutatorFixedOutput

/-!
# Weighted cutoff commutator of the generated physical precision

This module was validated from a cold checkout at source checkpoint
`6bef7974e800d80534e171a285a7ea5b90d324e4` by GitHub Actions run
`30994320564` against the pinned Lean/Mathlib environment.

This specializes the direct fixed-output commutator bridge to the literal
generated CMP99 precision.  The covariant-Laplacian and normalized
`Q'^* Q'` budgets remain separate until the final addition.  The cutoff is
still an arbitrary Lipschitz function on the active carrier: identifying it
with the source large-block profile is a subsequent, visible dictionary.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator RealInnerProductSpace

noncomputable section

variable {d M N Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero N] [NeZero Nc]

/-- Cutoff-commutator budget carried by the covariant-Laplacian summand. -/
noncomputable def cmp99SourceGeneratedPhysicalLaplacianCutoffBudget
    (d M depth : ℕ) (spacing rate slope : ℝ) : ℝ :=
  slope * (M ^ (depth + 1) : ℝ) *
    cmp99ActiveRegionSourceCovariantLaplacianWeightedRowAmplitude
      d spacing rate

/-- Cutoff-commutator budget carried by the normalized `Q'^* Q'` summand. -/
noncomputable def cmp99SourceGeneratedPhysicalMassCutoffBudget
    (d M depth : ℕ) (spacing epsilon rate slope : ℝ) : ℝ :=
  slope * (M ^ (depth + 1) : ℝ) *
    (|cmp99SourceGeneratedPhysicalMass d M (depth + 1) spacing epsilon| *
      (Real.exp (rate * ((M ^ (depth + 1) - 1 : ℕ) : ℝ)) *
        (cmp99SourceBlockAverageWeight M d) ^ (depth + 1)))

/-- Literal sum of the two physically distinct commutator budgets. -/
noncomputable def cmp99SourceGeneratedPhysicalCutoffCommutatorBudget
    (d M depth : ℕ) (spacing epsilon rate slope : ℝ) : ℝ :=
  cmp99SourceGeneratedPhysicalLaplacianCutoffBudget
      d M depth spacing rate slope +
    cmp99SourceGeneratedPhysicalMassCutoffBudget
      d M depth spacing epsilon rate slope

/-- Direct fixed-output weighted estimate for the cutoff commutator of the
literal generated physical precision.  The only cutoff input is its local
Lipschitz estimate; the precision, range, and two row budgets are constructed
internally. -/
theorem cmp99SourceGeneratedPhysicalPrecision_cutoffCommutator_fixedOutputWeighted
    (hd : 2 ≤ d) (hM : 2 ≤ M) (Omega : ActiveGaugeRegion d N)
    (depth : ℕ) {spacing epsilon rate slope : ℝ}
    (hspacing : 0 < spacing) (hrate : 0 ≤ rate) (hslope : 0 ≤ slope)
    (background : GaugeConfig d
      (cmp99RegionalLatticeSize M N (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget d M Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge d
      (cmp99RegionalLatticeSize M N (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (h : ActiveGaugeRegion.Site
      (cmp99IteratedLiftActiveRegion (M := M) Omega (depth + 1)) → ℝ)
    (hLipschitz : ∀ target source,
      ‖h target - h source‖ ≤
        slope * (finBoxDist target.1 source.1 : ℝ)) :
    FinitePiLpTypedFixedOutputWeightedKernelBound
      (finitePiLpScalarCommutator
        (ι := ActiveGaugeRegion.Site
          (cmp99IteratedLiftActiveRegion (M := M) Omega (depth + 1)))
        (g := SUNLieCoord Nc) h
        (cmp99SourceGeneratedPhysicalPrecision hd hM Omega depth spacing epsilon
          background budget fineSmall))
      (fun (target source : ActiveGaugeRegion.Site
          (cmp99IteratedLiftActiveRegion (M := M) Omega (depth + 1))) =>
        finBoxDist target.1 source.1)
      (cmp99SourceGeneratedPhysicalCutoffCommutatorBudget
        d M depth spacing epsilon rate slope) rate := by
  let K := cmp99SourceGeneratedPhysicalPrecision hd hM Omega depth
    spacing epsilon background budget fineSmall
  let dist := fun target source : ActiveGaugeRegion.Site
      (cmp99IteratedLiftActiveRegion (M := M) Omega (depth + 1)) =>
    finBoxDist target.1 source.1
  have hfinite : FinitePiLpTypedFiniteRange K dist (M ^ (depth + 1)) := by
    simpa [K, dist, FinitePiLpTypedFiniteRange, FinitePiLpFiniteRange] using
      cmp99SourceGeneratedPhysicalPrecision_finiteRange hd hM Omega depth
        spacing epsilon background budget fineSmall
  have hrow : FinitePiLpTypedFixedOutputWeightedKernelBound K dist
      (cmp99SourceGeneratedPhysicalPrecisionDirectWeightedRowAmplitude
        d M depth spacing epsilon rate) rate := by
    simpa [K, dist] using
      cmp99SourceGeneratedPhysicalPrecision_directFixedOutputWeighted
        hd hM Omega depth hspacing hrate background budget fineSmall
  have hcomm :=
    finitePiLpTypedFixedOutputWeightedKernelBound_scalarCommutator
      h K dist (M ^ (depth + 1)) hslope hfinite hLipschitz hrow
  simpa [finitePiLpScalarCommutator, K, dist,
    cmp99SourceGeneratedPhysicalCutoffCommutatorBudget,
    cmp99SourceGeneratedPhysicalLaplacianCutoffBudget,
    cmp99SourceGeneratedPhysicalMassCutoffBudget,
    cmp99SourceGeneratedPhysicalPrecisionDirectWeightedRowAmplitude,
    mul_add] using hcomm

/-- Pointwise exponential form of the same physical commutator estimate. -/
theorem cmp99SourceGeneratedPhysicalPrecision_cutoffCommutator_exponentialKernelBound
    (hd : 2 ≤ d) (hM : 2 ≤ M) (Omega : ActiveGaugeRegion d N)
    (depth : ℕ) {spacing epsilon rate slope : ℝ}
    (hspacing : 0 < spacing) (hrate : 0 < rate) (hslope : 0 ≤ slope)
    (background : GaugeConfig d
      (cmp99RegionalLatticeSize M N (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget d M Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge d
      (cmp99RegionalLatticeSize M N (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (h : ActiveGaugeRegion.Site
      (cmp99IteratedLiftActiveRegion (M := M) Omega (depth + 1)) → ℝ)
    (hLipschitz : ∀ target source,
      ‖h target - h source‖ ≤
        slope * (finBoxDist target.1 source.1 : ℝ)) :
    FinitePiLpTypedExponentialKernelBound
      (finitePiLpScalarCommutator
        (ι := ActiveGaugeRegion.Site
          (cmp99IteratedLiftActiveRegion (M := M) Omega (depth + 1)))
        (g := SUNLieCoord Nc) h
        (cmp99SourceGeneratedPhysicalPrecision hd hM Omega depth spacing epsilon
          background budget fineSmall))
      (fun (target source : ActiveGaugeRegion.Site
          (cmp99IteratedLiftActiveRegion (M := M) Omega (depth + 1))) =>
        finBoxDist target.1 source.1)
      (cmp99SourceGeneratedPhysicalCutoffCommutatorBudget
        d M depth spacing epsilon rate slope) rate := by
  apply finitePiLpTypedExponentialKernelBound_of_fixedOutputWeighted _ _ hrate
  exact
    cmp99SourceGeneratedPhysicalPrecision_cutoffCommutator_fixedOutputWeighted
      hd hM Omega depth hspacing hrate.le hslope background budget fineSmall h
      hLipschitz

end

end YangMills.RG
