/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP95PeriodicSquareTorusSlope
import YangMills.RG.BalabanCMP99SourceGeneratedSmoothGreenCommutator

/-!
# The corrected fine CMP99 commutator `[G',(h'_Pi)^2]`

The older generated commutator retained a free coordinate chart and the
one-extra-`M` scale.  Here the multiplier is the literal corrected fine
square partition at side `2*M^(depth+1)`.  Its boundary-safe torus slope is
generated internally, so neither a chart nor a Lipschitz premise remains.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator RealInnerProductSpace

noncomputable section

set_option maxHeartbeats 4000000
set_option maxRecDepth 4000

variable {M Nc Q depth : ℕ}
variable [NeZero M] [NeZero Nc] [NeZero Q]

/-- Literal corrected fine operator `[G',(h'_Pi)^2]` on the generated active
region. -/
noncomputable def cmp99SourceGeneratedPhysicalGreenFineSquareCommutator
    (P : CMP95SourceSmoothPartitionProfile)
    (Omega : ActiveGaugeRegion 4 (2 * Q))
    (cell : FinBox 4 Q)
    (hM : 2 ≤ M) {spacing epsilon : ℝ} (hspacing : 0 < spacing)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 M Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff 4 M (depth + 1)
      spacing epsilon < 1) :=
  let G := cmp99SourceGeneratedPhysicalGreen
    (show 2 ≤ 4 by norm_num) hM Omega depth hspacing background budget
      fineSmall hsmall
  finitePiLpOperatorScalarCommutator G fun x =>
    cmp99SourceGeneratedFineCellSquareWeight P M Q depth cell x.1

/-- Pointwise exponential localization of the corrected fine commutator.
The explicit `32/M0` slope and physical Green estimate are both produced
inside the proof. -/
theorem cmp99SourceGeneratedPhysicalGreenFineSquareCommutator_exponential
    (P : CMP95SourceSmoothPartitionProfile)
    (Omega : ActiveGaugeRegion 4 (2 * Q))
    (cell : FinBox 4 Q)
    (hM : 2 ≤ M) {spacing epsilon : ℝ} (hspacing : 0 < spacing)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 M Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff 4 M (depth + 1)
      spacing epsilon < 1) :
    FinitePiLpExponentialKernelBound
      (cmp99SourceGeneratedPhysicalGreenFineSquareCommutator
        P Omega cell hM hspacing background budget fineSmall hsmall)
      (fun x y => finBoxDist x.1 y.1)
      ((2 * ((32 * P.derivBound) /
          cmp99SourceGeneratedCellCutoffScale M depth) *
            (2 / cmp99SourceGeneratedCoercivity
              4 M (depth + 1) spacing epsilon)) /
        cmp99SourceGeneratedCombesThomasRate 4 M depth spacing epsilon)
      (cmp99SourceGeneratedCombesThomasRate
        4 M depth spacing epsilon / 2) := by
  unfold cmp99SourceGeneratedPhysicalGreenFineSquareCommutator
  rw [finitePiLpOperatorScalarCommutator_eq_neg]
  apply finitePiLpTypedExponentialKernelBound_neg
  apply finitePiLpScalarCommutator_exponentialKernelBound_of_lipschitz
    (h := fun x =>
      cmp99SourceGeneratedFineCellSquareWeight P M Q depth cell x.1)
    (A := cmp99SourceGeneratedPhysicalGreen
      (show 2 ≤ 4 by norm_num) hM Omega depth hspacing background budget
        fineSmall hsmall)
    (dist := fun x y => finBoxDist x.1 y.1)
  · exact div_nonneg (mul_nonneg (by norm_num) P.derivBound_nonneg)
      (cmp99SourceGeneratedCellCutoffScale_pos M depth).le
  · intro target source
    simpa only [finBoxDist_comm target.1 source.1] using
      norm_cmp99SourceGeneratedFineCellSquareWeight_finBox_sub_le
        P M Q depth cell source.1 target.1
  · exact cmp99SourceGeneratedPhysicalGreen_canonicalExponentialKernelBound
      (show 2 ≤ 4 by norm_num) hM Omega depth hspacing background budget
        fineSmall hsmall

/-- Volume-independent operator norm of the corrected fine commutator. -/
theorem norm_cmp99SourceGeneratedPhysicalGreenFineSquareCommutator_le
    (P : CMP95SourceSmoothPartitionProfile)
    (Omega : ActiveGaugeRegion 4 (2 * Q))
    (cell : FinBox 4 Q)
    (hM : 2 ≤ M) {spacing epsilon : ℝ} (hspacing : 0 < spacing)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 M Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff 4 M (depth + 1)
      spacing epsilon < 1) :
    ‖cmp99SourceGeneratedPhysicalGreenFineSquareCommutator
        P Omega cell hM hspacing background budget fineSmall hsmall‖ ≤
      ((2 * ((32 * P.derivBound) /
          cmp99SourceGeneratedCellCutoffScale M depth) *
            (2 / cmp99SourceGeneratedCoercivity
              4 M (depth + 1) spacing epsilon)) /
        cmp99SourceGeneratedCombesThomasRate 4 M depth spacing epsilon) *
      cmp99OmegaSiteExpSumBound
        (cmp99SourceGeneratedCombesThomasRate
          4 M depth spacing epsilon / 2) := by
  let rate := cmp99SourceGeneratedCombesThomasRate
    4 M depth spacing epsilon
  have hrate : 0 < rate :=
    cmp99SourceGeneratedCombesThomasRate_pos 4 M depth hspacing hsmall
  have hrowNonneg : 0 ≤ cmp99OmegaSiteExpSumBound (rate / 2) := by
    unfold cmp99OmegaSiteExpSumBound
    exact tsum_nonneg fun _ => mul_nonneg (by positivity) (Real.exp_pos _).le
  apply finitePiLpOpNorm_le_of_exponentialKernelBound
    _ (fun x y => finBoxDist x.1 y.1)
    (fun x y => finBoxDist_comm x.1 y.1) hrowNonneg
  · exact cmp99SourceGeneratedPhysicalGreenFineSquareCommutator_exponential
      P Omega cell hM hspacing background budget fineSmall hsmall
  · intro x
    exact activeGaugeRegion_finBoxDist_exp_sum_le
      (cmp99IteratedLiftActiveRegion (M := M) Omega (depth + 1)) x
      (div_pos hrate zero_lt_two)

end

end YangMills.RG
