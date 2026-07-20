/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceGeneratedSectionCSmoothBasicFactor
import YangMills.RG.FinitePiLpTypedWeightedRowKernel

/-!
# Fixed-rate decay of the smooth CMP99 basic factor

CMP99 printed p. 412 uses `K(h'_Pi) G'_Pi h'_Pi`.  The exact identity

`K(h) G h = Delta' [G,h] h`

separates a finite-range precision from the smooth Green commutator.  This
module combines their source-generated estimates in a weighted-row norm at
one fixed rate.  The precision cost uses only its finite range ball; the
commutator retains the `M0^-1` derivative gain from CMP95 (1.118).
-/

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator RealInnerProductSpace

noncomputable section

universe v

variable {M Nc Q j : ℕ} [NeZero M] [NeZero Nc] [NeZero Q]
variable {cell : FinBox 4 Q}
variable {ScaleSite : Fin (j + 2) → Type v}
variable [∀ r, DecidableEq (ScaleSite r)]
variable {Scaled : CMP99SourceScaledStratification
  (FinBox 4 (2 * Q)) (j + 2) ScaleSite}
variable {dist : FinBox 4 (2 * Q) → FinBox 4 (2 * Q) → ℕ}
variable {gap : Fin (j + 1) → ℕ}

set_option maxRecDepth 3000
set_option maxHeartbeats 6000000

/-- Local fixed-rate row cost of the generated precision. -/
noncomputable def cmp99SourceGeneratedPhysicalPrecisionWeightedRowAmplitude
    (M depth : ℕ) (spacing epsilon rate : ℝ) : ℝ :=
  cmp99SourceGeneratedPhysicalPrecisionUpperBound
      4 M (depth + 1) spacing epsilon *
    Real.exp (rate * (M ^ (depth + 1) : ℕ)) *
    (((2 * M ^ (depth + 1) + 1) ^ 4 : ℕ) : ℝ)

/-- Pointwise amplitude of the unsquared smooth Green commutator before its
volume-independent exponential row sum is taken. -/
noncomputable def cmp99SourceGeneratedSmoothGreenLinearCommutatorPointAmplitude
    (P : CMP95SourceSmoothPartitionProfile)
    (M depth : ℕ) (spacing epsilon : ℝ) : ℝ :=
  (2 * ((P.derivBound /
      cmp99SourceGeneratedSmoothCutoffScale M depth) * 4) *
        (2 / cmp99SourceGeneratedCoercivity
          4 M (depth + 1) spacing epsilon)) /
    cmp99SourceGeneratedCombesThomasRate 4 M depth spacing epsilon

/-- Fixed-rate row cost of `[G',h'_Pi]h'_Pi`. -/
noncomputable def cmp99SourceGeneratedSmoothGreenCutoffWeightedRowAmplitude
    (P : CMP95SourceSmoothPartitionProfile)
    (M depth : ℕ) (spacing epsilon rate : ℝ) : ℝ :=
  cmp99SourceGeneratedSmoothGreenLinearCommutatorPointAmplitude
      P M depth spacing epsilon *
    cmp99OmegaSiteExpSumBound
      (cmp99SourceGeneratedCombesThomasRate
        4 M depth spacing epsilon / 2 - rate)

/-- Complete fixed-rate row amplitude of `K(h')G'h'`. -/
noncomputable def cmp99SourceGeneratedSmoothFineBasicWeightedRowAmplitude
    (P : CMP95SourceSmoothPartitionProfile)
    (M depth : ℕ) (spacing epsilon rate : ℝ) : ℝ :=
  cmp99SourceGeneratedPhysicalPrecisionWeightedRowAmplitude
      M depth spacing epsilon rate *
    cmp99SourceGeneratedSmoothGreenCutoffWeightedRowAmplitude
      P M depth spacing epsilon rate

/-- The literal generated precision has a volume-independent weighted row at
every nonnegative fixed rate. -/
theorem cmp99SourceGeneratedPhysicalPrecision_weightedRowKernelBound
    (Omega : ActiveGaugeRegion 4 (2 * Q))
    (hM : 2 ≤ M) (depth : ℕ) {spacing epsilon rate : ℝ}
    (hspacing : 0 < spacing) (hrate : 0 ≤ rate)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 M Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon) :
    FinitePiLpTypedWeightedRowKernelBound
      (cmp99SourceGeneratedPhysicalPrecision
        (show 2 ≤ 4 by norm_num) hM Omega depth spacing epsilon background
          budget fineSmall)
      (fun target source => finBoxDist target.1 source.1)
      (cmp99SourceGeneratedPhysicalPrecisionWeightedRowAmplitude
        M depth spacing epsilon rate) rate := by
  let Omega' := cmp99IteratedLiftActiveRegion (M := M) Omega (depth + 1)
  let Precision := cmp99SourceGeneratedPhysicalPrecision
    (show 2 ≤ 4 by norm_num) hM Omega depth spacing epsilon background budget
      fineSmall
  let B := cmp99SourceGeneratedPhysicalPrecisionUpperBound
    4 M (depth + 1) spacing epsilon
  have hB : 0 ≤ B :=
    (cmp99SourceGeneratedPhysicalPrecisionUpperBound_pos
      4 M (depth + 1) hspacing).le
  have hrange : FinitePiLpTypedFiniteRange Precision
      (fun target source => finBoxDist target.1 source.1)
      (M ^ (depth + 1)) := by
    exact cmp99SourceGeneratedPhysicalPrecision_finiteRange
      (show 2 ≤ 4 by norm_num) hM Omega depth spacing epsilon background
        budget fineSmall
  have hkernel : FinitePiLpTypedKernelBound Precision (fun _ _ => B) := by
    exact cmp99SourceGeneratedPhysicalPrecision_kernelBound
      (show 2 ≤ 4 by norm_num) hM Omega depth hspacing background budget
        fineSmall
  have hcard : ∀ source : ActiveGaugeRegion.Site Omega',
      (Finset.univ.filter (fun target : ActiveGaugeRegion.Site Omega' =>
        finBoxDist target.1 source.1 ≤ M ^ (depth + 1))).card ≤
          (2 * M ^ (depth + 1) + 1) ^ 4 := by
    intro source
    simpa [finBoxDist_comm] using
      activeGaugeRegion_finBoxDist_ball_card_le Omega' source
        (M ^ (depth + 1))
  simpa [Precision, B,
    cmp99SourceGeneratedPhysicalPrecisionWeightedRowAmplitude] using
      finitePiLpTypedWeightedRowKernelBound_of_finiteRange Precision
        (fun target source => finBoxDist target.1 source.1)
        (M ^ (depth + 1)) ((2 * M ^ (depth + 1) + 1) ^ 4)
        hB hrate hrange hkernel hcard

namespace CMP99SourceDependentOmegaGeometry

set_option maxRecDepth 3000
set_option maxHeartbeats 6000000

/-- The complete literal p. 412 basic factor has a fixed-rate weighted row.
The only rate condition is that the chosen rate lie strictly below half the
generated Combes--Thomas rate. -/
theorem generatedCMP95SourceCenteredSmoothFineSectionCBasicFactor_weightedRow
    (D : CMP99SourceDependentOmegaGeometry
      (FinBox 4 (2 * Q)) j ScaleSite Scaled
      (cmp99SourceTildePiLargeBlocks cell 3)
      (cmp99SourceTildePiLargeBlocks cell 4) dist gap)
    (P : CMP95SourceSmoothPartitionProfile)
    (hpi5 : D.fineRegion (cmp99OmegaZeroIndex j) ⊆
      cmp99SourceTildePiLargeBlocks cell 5)
    (s : Fin (j + 2)) (hM : 2 ≤ M) (depth : ℕ)
    {spacing epsilon rate : ℝ} (hspacing : 0 < spacing) (hrate : 0 < rate)
    (hrateLt : rate < cmp99SourceGeneratedCombesThomasRate
      4 M depth spacing epsilon / 2)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 M Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff 4 M (depth + 1)
      spacing epsilon < 1) :
    let Omega := D.operatorCoarseRegion hpi5 s
    let Omega' := cmp99IteratedLiftActiveRegion (M := M) Omega (depth + 1)
    FinitePiLpTypedWeightedRowKernelBound
      (D.generatedCMP95SourceCenteredSmoothFineSectionCBasicFactor P hpi5 s
        hM depth hspacing background budget fineSmall hsmall)
      (fun target source : ActiveGaugeRegion.Site Omega' =>
        finBoxDist target.1 source.1)
      (cmp99SourceGeneratedSmoothFineBasicWeightedRowAmplitude
        P M depth spacing epsilon rate) rate := by
  dsimp only
  let Omega := D.operatorCoarseRegion hpi5 s
  let Omega' := cmp99IteratedLiftActiveRegion (M := M) Omega (depth + 1)
  let center := cmp99SourceGeneratedSmoothCutoffCenter M Q depth cell
  let h := fun x : ActiveGaugeRegion.Site Omega' =>
    P.tensorCutoff (cmp99SourceGeneratedSmoothCutoffScale M depth)
      (fun _ => 0) (finTorusDistanceCoordinates center x.1)
  let H := finitePiLpScalarMultiplier (g := SUNLieCoord Nc) h
  let Precision := cmp99SourceGeneratedPhysicalPrecision
    (show 2 ≤ 4 by norm_num) hM Omega depth spacing epsilon background budget
      fineSmall
  let C := cmp99SourceGeneratedPhysicalGreenSmoothCommutator
    P Omega (fun _ => 0) (fun x => finTorusDistanceCoordinates center x.1)
      hM hspacing background budget fineSmall hsmall
  let AP := cmp99SourceGeneratedPhysicalPrecisionWeightedRowAmplitude
    M depth spacing epsilon rate
  let AC := cmp99SourceGeneratedSmoothGreenLinearCommutatorPointAmplitude
    P M depth spacing epsilon
  let S := cmp99OmegaSiteExpSumBound
    (cmp99SourceGeneratedCombesThomasRate
      4 M depth spacing epsilon / 2 - rate)
  have hPrecision : FinitePiLpTypedWeightedRowKernelBound Precision
      (fun target source : ActiveGaugeRegion.Site Omega' =>
        finBoxDist target.1 source.1) AP rate := by
    simpa [Omega', Precision, AP] using
      cmp99SourceGeneratedPhysicalPrecision_weightedRowKernelBound Omega hM
        depth hspacing hrate.le background budget fineSmall
  have hCexp : FinitePiLpTypedExponentialKernelBound C
      (fun target source : ActiveGaugeRegion.Site Omega' =>
        finBoxDist target.1 source.1) AC
      (cmp99SourceGeneratedCombesThomasRate
        4 M depth spacing epsilon / 2) := by
    simpa [C, AC,
      cmp99SourceGeneratedSmoothGreenLinearCommutatorPointAmplitude] using
      cmp99SourceGeneratedPhysicalGreenSmoothCommutator_exponential
        P Omega (fun _ => 0)
          (fun x => finTorusDistanceCoordinates center x.1)
          (fun target source =>
            sum_norm_finTorusDistanceCoordinates_sub_le_four_finBoxDist
              center target.1 source.1)
          hM hspacing background budget fineSmall hsmall
  have hCHexp : FinitePiLpTypedExponentialKernelBound (C.comp H)
      (fun target source : ActiveGaugeRegion.Site Omega' =>
        finBoxDist target.1 source.1) AC
      (cmp99SourceGeneratedCombesThomasRate
        4 M depth spacing epsilon / 2) := by
    exact finitePiLpTypedExponentialKernelBound_comp_scalarMultiplier_right
      h C (fun x => P.norm_tensorCutoff_le_one _ _ _) hCexp
  have hgap : 0 < cmp99SourceGeneratedCombesThomasRate
      4 M depth spacing epsilon / 2 - rate := sub_pos.mpr hrateLt
  have hS : 0 ≤ S := by
    dsimp [S, cmp99OmegaSiteExpSumBound]
    exact tsum_nonneg fun _ => mul_nonneg (by positivity) (Real.exp_pos _).le
  have hsum : ∀ source : ActiveGaugeRegion.Site Omega',
      ∑ target : ActiveGaugeRegion.Site Omega',
        Real.exp (-((cmp99SourceGeneratedCombesThomasRate
          4 M depth spacing epsilon / 2 - rate) *
            (finBoxDist target.1 source.1 : ℝ))) ≤ S := by
    intro source
    have hs := activeGaugeRegion_finBoxDist_exp_sum_le Omega' source hgap
    simpa [S, finBoxDist_comm] using hs
  have hCH : FinitePiLpTypedWeightedRowKernelBound (C.comp H)
      (fun target source : ActiveGaugeRegion.Site Omega' =>
        finBoxDist target.1 source.1) (AC * S) rate :=
    finitePiLpTypedWeightedRowKernelBound_of_exponential
      (C.comp H) (fun target source => finBoxDist target.1 source.1)
      hrate.le hS hCHexp hsum
  rw [D.generatedCMP95SourceCenteredSmoothFineSectionCBasicFactor_eq_source
    P hpi5 s hM depth hspacing background budget fineSmall hsmall]
  simpa [AP, AC, S,
    cmp99SourceGeneratedSmoothFineBasicWeightedRowAmplitude,
    cmp99SourceGeneratedSmoothGreenCutoffWeightedRowAmplitude] using
      finitePiLpTypedWeightedRowKernelBound_comp
        (fun target middle : ActiveGaugeRegion.Site Omega' =>
          finBoxDist target.1 middle.1)
        (fun middle source : ActiveGaugeRegion.Site Omega' =>
          finBoxDist middle.1 source.1)
        (fun target source : ActiveGaugeRegion.Site Omega' =>
          finBoxDist target.1 source.1)
        (fun target middle source =>
          finBoxDist_triangle target.1 middle.1 source.1)
        hPrecision hCH

end CMP99SourceDependentOmegaGeometry

end
end YangMills.RG
