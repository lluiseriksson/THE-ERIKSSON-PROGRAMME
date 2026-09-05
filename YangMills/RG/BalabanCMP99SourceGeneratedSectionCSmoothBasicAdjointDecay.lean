/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceGeneratedWeightedAdjointRange
import YangMills.RG.BalabanCMP99SourceGeneratedSectionCSmoothBasicFactorDecay
import YangMills.RG.BalabanCMP99SourceGeneratedSectionCRightFactorNorm

/-!
# Fixed-rate decay of the mixed-scale smooth CMP99 basic factor

CMP99 printed p. 413 extends the p. 412 factor to

`K(h'_Pi) G'_Pi h'_Pi Q'^*`.

The generated weighted adjoint is first exposed in its literal terminal
coordinates.  Its exact terminal-block support and counting-norm bound give
a volume-independent weighted row.  Composing this row with the already
proved fixed-rate row of `K(h')G'h'` preserves the same spatial rate.
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

/-- Fixed-rate row cost of the complete generated source-weighted synthesis. -/
noncomputable def cmp99SourceGeneratedWeightedAdjointWeightedRowAmplitude
    (M depth : ℕ) (rate : ℝ) : ℝ :=
  let R := M ^ (depth + 1) - 1
  cmp99SourceGeneratedWeightedAdjointNormBound M depth *
    Real.exp (rate * (R : ℝ)) * (((2 * R + 1) ^ 4 : ℕ) : ℝ)

/-- Complete fixed-rate row cost of the physical p. 413 mixed-scale factor. -/
noncomputable def cmp99SourceGeneratedSmoothBasicAdjointWeightedRowAmplitude
    (P : CMP95SourceSmoothPartitionProfile)
    (M depth : ℕ) (spacing epsilon rate : ℝ) : ℝ :=
  cmp99SourceGeneratedSmoothFineBasicWeightedRowAmplitude
      P M depth spacing epsilon rate *
    cmp99SourceGeneratedWeightedAdjointWeightedRowAmplitude M depth rate

namespace CMP99SourceDependentOmegaGeometry

set_option maxRecDepth 3000
set_option maxHeartbeats 6000000

/-- The coordinate-exposed generated weighted adjoint has a fixed-rate row
whose support cost is one literal order-`M^(depth+1)` terminal block. -/
theorem generatedPhysicalWeightedAdjoint_weightedRow
    (D : CMP99SourceDependentOmegaGeometry
      (FinBox 4 (2 * Q)) j ScaleSite Scaled
      (cmp99SourceTildePiLargeBlocks cell 3)
      (cmp99SourceTildePiLargeBlocks cell 4) dist gap)
    (hpi5 : D.fineRegion (cmp99OmegaZeroIndex j) ⊆
      cmp99SourceTildePiLargeBlocks cell 5)
    (s : Fin (j + 2)) (hM : 2 ≤ M) (depth : ℕ)
    {spacing epsilon rate : ℝ} (hspacing : 0 < spacing) (hrate : 0 ≤ rate)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 M Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon) :
    let Omega := D.operatorCoarseRegion hpi5 s
    let regions := cmp99SourceIteratedLiftActiveRegionChain
      (M := M) Omega (depth + 1)
    let W := regions.physicalWeightedAdjoint (show 2 ≤ 4 by norm_num) hM
      (matrixSUNAdjointModel Nc) spacing epsilon background
      budget.toRadiusChain fineSmall
    FinitePiLpTypedWeightedRowKernelBound W
      (fun target source => finBoxDist target.1
        (regions.terminalRepresentative source).1)
      (cmp99SourceGeneratedWeightedAdjointWeightedRowAmplitude M depth rate)
      rate := by
  dsimp only
  let Omega := D.operatorCoarseRegion hpi5 s
  let regions := cmp99SourceIteratedLiftActiveRegionChain
    (M := M) Omega (depth + 1)
  let W := regions.physicalWeightedAdjoint (show 2 ≤ 4 by norm_num) hM
    (matrixSUNAdjointModel Nc) spacing epsilon background
    budget.toRadiusChain fineSmall
  let beta := cmp99SourceGeneratedWeightedAdjointNormBound M depth
  let R := M ^ (depth + 1) - 1
  have hnormT :
      ‖(regions.weightedQprimeTower (show 2 ≤ 4 by norm_num) hM
        (matrixSUNAdjointModel Nc) spacing epsilon background
        budget.toRadiusChain fineSmall).weightedAdjoint‖ ≤ beta := by
    simpa [Omega, regions, beta] using
      D.norm_generatedWeightedAdjoint_le hpi5 s hM depth hspacing background
        budget fineSmall
  have hnormW : ‖W‖ ≤ beta := by
    calc
      ‖W‖ =
          ‖(regions.weightedQprimeTower (show 2 ≤ 4 by norm_num) hM
            (matrixSUNAdjointModel Nc) spacing epsilon background
            budget.toRadiusChain fineSmall).weightedAdjoint‖ := by
        simpa [W] using regions.norm_physicalWeightedAdjoint
          (show 2 ≤ 4 by norm_num) hM (matrixSUNAdjointModel Nc)
          spacing epsilon background budget.toRadiusChain fineSmall
      _ ≤ beta := hnormT
  have hbeta : 0 ≤ beta := (norm_nonneg W).trans hnormW
  have hrange : FinitePiLpTypedFiniteRange W
      (fun target source => finBoxDist target.1
        (regions.terminalRepresentative source).1) R := by
    simpa [Omega, regions, W, R] using
      cmp99SourceIteratedLift_physicalWeightedAdjoint_finiteRange
        (M := M) Omega (depth + 1) (show 2 ≤ 4 by norm_num) hM
        (matrixSUNAdjointModel Nc) spacing epsilon background
        budget.toRadiusChain fineSmall
  have hkernel : FinitePiLpTypedKernelBound W (fun _ _ => beta) := by
    intro source target v
    calc
      ‖W (singleFinitePiLp source v) target‖ ≤ ‖W‖ * ‖v‖ :=
        finitePiLpTypedKernelBound_const_opNorm W source target v
      _ ≤ beta * ‖v‖ :=
        mul_le_mul_of_nonneg_right hnormW (norm_nonneg v)
  have hcard : ∀ source : regions.terminalSite,
      (Finset.univ.filter (fun target : ActiveGaugeRegion.Site
        (cmp99IteratedLiftActiveRegion (M := M) Omega (depth + 1)) =>
          finBoxDist target.1 (regions.terminalRepresentative source).1 ≤ R)).card ≤
        (2 * R + 1) ^ 4 := by
    intro source
    simpa [finBoxDist_comm] using
      activeGaugeRegion_finBoxDist_ball_card_le
        (cmp99IteratedLiftActiveRegion (M := M) Omega (depth + 1))
        (regions.terminalRepresentative source) R
  simpa [W, beta, R,
    cmp99SourceGeneratedWeightedAdjointWeightedRowAmplitude] using
      finitePiLpTypedWeightedRowKernelBound_of_finiteRange W
        (fun target source => finBoxDist target.1
          (regions.terminalRepresentative source).1)
        R ((2 * R + 1) ^ 4) hbeta hrate hrange hkernel hcard

/-- Literal coordinate-exposed realization of the mixed-scale p. 413 factor
`K(h'_Pi)G'_Pi h'_Pi Q'^*`. -/
noncomputable def generatedCMP95SourceCenteredSmoothPhysicalBasicAdjointFactor
    (D : CMP99SourceDependentOmegaGeometry
      (FinBox 4 (2 * Q)) j ScaleSite Scaled
      (cmp99SourceTildePiLargeBlocks cell 3)
      (cmp99SourceTildePiLargeBlocks cell 4) dist gap)
    (P : CMP95SourceSmoothPartitionProfile)
    (hpi5 : D.fineRegion (cmp99OmegaZeroIndex j) ⊆
      cmp99SourceTildePiLargeBlocks cell 5)
    (s : Fin (j + 2)) (hM : 2 ≤ M) (depth : ℕ)
    {spacing epsilon : ℝ} (hspacing : 0 < spacing)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 M Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff 4 M (depth + 1)
      spacing epsilon < 1) := by
  let Omega := D.operatorCoarseRegion hpi5 s
  let regions := cmp99SourceIteratedLiftActiveRegionChain
    (M := M) Omega (depth + 1)
  let Basic := D.generatedCMP95SourceCenteredSmoothFineSectionCBasicFactor
    P hpi5 s hM depth hspacing background budget fineSmall hsmall
  let W := regions.physicalWeightedAdjoint (show 2 ≤ 4 by norm_num) hM
    (matrixSUNAdjointModel Nc) spacing epsilon background
    budget.toRadiusChain fineSmall
  exact Basic.comp W

/-- The original bundled p. 413 factor transported only along the proved
equality between its generated terminal bundle and the exposed physical
coordinate bundle. -/
noncomputable def transportedGeneratedCMP95SourceCenteredSmoothBasicAdjointFactor
    (D : CMP99SourceDependentOmegaGeometry
      (FinBox 4 (2 * Q)) j ScaleSite Scaled
      (cmp99SourceTildePiLargeBlocks cell 3)
      (cmp99SourceTildePiLargeBlocks cell 4) dist gap)
    (P : CMP95SourceSmoothPartitionProfile)
    (hpi5 : D.fineRegion (cmp99OmegaZeroIndex j) ⊆
      cmp99SourceTildePiLargeBlocks cell 5)
    (s : Fin (j + 2)) (hM : 2 ≤ M) (depth : ℕ)
    {spacing epsilon : ℝ} (hspacing : 0 < spacing)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 M Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff 4 M (depth + 1)
      spacing epsilon < 1) := by
  let Omega := D.operatorCoarseRegion hpi5 s
  let regions := cmp99SourceIteratedLiftActiveRegionChain
    (M := M) Omega (depth + 1)
  let Omega' := cmp99IteratedLiftActiveRegion (M := M) Omega (depth + 1)
  let T := regions.weightedQprimeTower (show 2 ≤ 4 by norm_num) hM
    (matrixSUNAdjointModel Nc) spacing epsilon background
    budget.toRadiusChain fineSmall
  let hT : T.TerminalSpace = regions.terminalHilbertSpace Nc :=
    regions.weightedQprimeTower_terminalSpace_eq (show 2 ≤ 4 by norm_num) hM
      (matrixSUNAdjointModel Nc) spacing epsilon background
      budget.toRadiusChain fineSmall
  let hCoord : regions.terminalHilbertSpace Nc =
      regions.terminalCoordinateHilbertSpace (Nc := Nc) :=
    regions.terminalHilbertSpace_eq_coordinate
  exact cmp99SourceTerminalCLMTransport
    (E := T.TerminalSpace)
    (F := cmp99SourcePhysicalTerminalHilbertSpace Nc Omega')
    (E' := regions.terminalCoordinateHilbertSpace (Nc := Nc))
    (F' := cmp99SourcePhysicalTerminalHilbertSpace Nc Omega')
    (hT.trans hCoord) rfl
    (D.generatedCMP95SourceCenteredSmoothSectionCBasicAdjointFactor P hpi5 s
      hM depth hspacing background budget fineSmall hsmall)

/-- The coordinate-exposed physical factor is exactly the previously
generated source factor after the canonical terminal-bundle transport. -/
theorem generatedCMP95SourceCenteredSmoothPhysicalBasicAdjointFactor_eq_transported
    (D : CMP99SourceDependentOmegaGeometry
      (FinBox 4 (2 * Q)) j ScaleSite Scaled
      (cmp99SourceTildePiLargeBlocks cell 3)
      (cmp99SourceTildePiLargeBlocks cell 4) dist gap)
    (P : CMP95SourceSmoothPartitionProfile)
    (hpi5 : D.fineRegion (cmp99OmegaZeroIndex j) ⊆
      cmp99SourceTildePiLargeBlocks cell 5)
    (s : Fin (j + 2)) (hM : 2 ≤ M) (depth : ℕ)
    {spacing epsilon : ℝ} (hspacing : 0 < spacing)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 M Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff 4 M (depth + 1)
      spacing epsilon < 1) :
    D.generatedCMP95SourceCenteredSmoothPhysicalBasicAdjointFactor P hpi5 s
        hM depth hspacing background budget fineSmall hsmall =
      D.transportedGeneratedCMP95SourceCenteredSmoothBasicAdjointFactor P hpi5
        s hM depth hspacing background budget fineSmall hsmall := by
  let Omega := D.operatorCoarseRegion hpi5 s
  let regions := cmp99SourceIteratedLiftActiveRegionChain
    (M := M) Omega (depth + 1)
  let Omega' := cmp99IteratedLiftActiveRegion (M := M) Omega (depth + 1)
  let T := regions.weightedQprimeTower (show 2 ≤ 4 by norm_num) hM
    (matrixSUNAdjointModel Nc) spacing epsilon background
    budget.toRadiusChain fineSmall
  let Basic := D.generatedCMP95SourceCenteredSmoothFineSectionCBasicFactor P
    hpi5 s hM depth hspacing background budget fineSmall hsmall
  let hT : T.TerminalSpace = regions.terminalHilbertSpace Nc :=
    regions.weightedQprimeTower_terminalSpace_eq (show 2 ≤ 4 by norm_num) hM
      (matrixSUNAdjointModel Nc) spacing epsilon background
      budget.toRadiusChain fineSmall
  let hCoord : regions.terminalHilbertSpace Nc =
      regions.terminalCoordinateHilbertSpace (Nc := Nc) :=
    regions.terminalHilbertSpace_eq_coordinate
  rw [generatedCMP95SourceCenteredSmoothPhysicalBasicAdjointFactor,
    regions.physicalWeightedAdjoint_eq_transported
      (show 2 ≤ 4 by norm_num) hM (matrixSUNAdjointModel Nc) spacing epsilon
        background budget.toRadiusChain fineSmall]
  have hcomp := cmp99SourceTerminalCLMTransport_comp
    (E := T.TerminalSpace)
    (F := cmp99SourcePhysicalTerminalHilbertSpace Nc Omega')
    (G := cmp99SourcePhysicalTerminalHilbertSpace Nc Omega')
    (E' := regions.terminalCoordinateHilbertSpace (Nc := Nc))
    (F' := cmp99SourcePhysicalTerminalHilbertSpace Nc Omega')
    (G' := cmp99SourcePhysicalTerminalHilbertSpace Nc Omega')
    (hT.trans hCoord) rfl rfl Basic T.weightedAdjoint
  simpa [CMP99SourceActiveRegionChain.transportedWeightedAdjoint,
    transportedGeneratedCMP95SourceCenteredSmoothBasicAdjointFactor,
    generatedCMP95SourceCenteredSmoothSectionCBasicAdjointFactor,
    Omega, Omega', regions, T, Basic, hT, hCoord] using hcomp

/-- The physical p. 413 mixed-scale factor preserves one fixed row-decay
rate and has no ambient-volume cost. -/
theorem generatedCMP95SourceCenteredSmoothPhysicalBasicAdjointFactor_weightedRow
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
    let regions := cmp99SourceIteratedLiftActiveRegionChain
      (M := M) Omega (depth + 1)
    FinitePiLpTypedWeightedRowKernelBound
      (D.generatedCMP95SourceCenteredSmoothPhysicalBasicAdjointFactor P hpi5
        s hM depth hspacing background budget fineSmall hsmall)
      (fun target source => finBoxDist target.1
        (regions.terminalRepresentative source).1)
      (cmp99SourceGeneratedSmoothBasicAdjointWeightedRowAmplitude
        P M depth spacing epsilon rate) rate := by
  dsimp only
  let Omega := D.operatorCoarseRegion hpi5 s
  let regions := cmp99SourceIteratedLiftActiveRegionChain
    (M := M) Omega (depth + 1)
  let Omega' := cmp99IteratedLiftActiveRegion (M := M) Omega (depth + 1)
  let Basic := D.generatedCMP95SourceCenteredSmoothFineSectionCBasicFactor
    P hpi5 s hM depth hspacing background budget fineSmall hsmall
  let W := regions.physicalWeightedAdjoint (show 2 ≤ 4 by norm_num) hM
    (matrixSUNAdjointModel Nc) spacing epsilon background
    budget.toRadiusChain fineSmall
  have hBasic :=
    D.generatedCMP95SourceCenteredSmoothFineSectionCBasicFactor_weightedRow
      P hpi5 s hM depth hspacing hrate hrateLt background budget fineSmall hsmall
  have hW := D.generatedPhysicalWeightedAdjoint_weightedRow hpi5 s hM depth
    hspacing hrate.le background budget fineSmall
  unfold generatedCMP95SourceCenteredSmoothPhysicalBasicAdjointFactor
  simpa [Omega, regions, Omega', Basic, W,
    cmp99SourceGeneratedSmoothBasicAdjointWeightedRowAmplitude] using
      finitePiLpTypedWeightedRowKernelBound_comp
        (fun target middle : ActiveGaugeRegion.Site Omega' =>
          finBoxDist target.1 middle.1)
        (fun middle : ActiveGaugeRegion.Site Omega' => fun source =>
          finBoxDist middle.1 (regions.terminalRepresentative source).1)
        (fun target : ActiveGaugeRegion.Site Omega' => fun source =>
          finBoxDist target.1 (regions.terminalRepresentative source).1)
        (fun target middle source =>
          finBoxDist_triangle target.1 middle.1
            (regions.terminalRepresentative source).1)
        hBasic hW

end CMP99SourceDependentOmegaGeometry

end
end YangMills.RG
