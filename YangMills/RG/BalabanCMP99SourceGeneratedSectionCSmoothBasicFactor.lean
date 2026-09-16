/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceGeneratedSectionCBasicFactor
import YangMills.RG.BalabanCMP99SourceGeneratedSmoothGreenCommutator

/-!
# The smooth basic CMP99 Section C factor

CMP99 printed p. 412 lists the basic generalized-walk factor

`K(h'_Pi) G'_Pi h'_Pi`,  with  `K(h) = h Delta' - Delta' h`.

The older generated factor used a block-constant cutoff and therefore did not
retain the small derivative scale asserted in (3.89).  Here the cutoff is the
literal CMP95 (1.118) tensor profile at scale `M^(depth+2)`.  The exact
resolvent identity

`K(h) G h = Delta' [G,h] h`

reduces its norm to the already generated Combes--Thomas estimate for `G` and
the source `M0^-1` cutoff slope.  No commutator estimate is supplied by the
caller.

The source reference is CMP99 printed pp. 412--413 (the basic factor and its
mixed-scale extension) together with CMP95 printed p. 36, equation (1.118)
(the smooth square partition).
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

/-- Explicit norm of the unsquared smooth Green commutator. -/
noncomputable def cmp99SourceGeneratedSmoothGreenLinearCommutatorNormBound
    (P : CMP95SourceSmoothPartitionProfile)
    (M depth : ℕ) (spacing epsilon : ℝ) : ℝ :=
  ((2 * ((P.derivBound /
      cmp99SourceGeneratedSmoothCutoffScale M depth) * 4) *
        (2 / cmp99SourceGeneratedCoercivity
          4 M (depth + 1) spacing epsilon)) /
    cmp99SourceGeneratedCombesThomasRate 4 M depth spacing epsilon) *
  cmp99OmegaSiteExpSumBound
    (cmp99SourceGeneratedCombesThomasRate
      4 M depth spacing epsilon / 2)

/-- Volume-independent norm budget for the smooth source basic factor.  Its
first factor is the generated precision norm; the second retains `M0^-1`. -/
noncomputable def cmp99SourceGeneratedSmoothFineBasicFactorNormBound
    (P : CMP95SourceSmoothPartitionProfile)
    (M depth : ℕ) (spacing epsilon : ℝ) : ℝ :=
  cmp99SourceGeneratedPhysicalPrecisionUpperBound
      4 M (depth + 1) spacing epsilon *
    cmp99SourceGeneratedSmoothGreenLinearCommutatorNormBound
      P M depth spacing epsilon

/-- Norm budget for the printed mixed-scale extension
`K(h') G' h' Q'^*`. -/
noncomputable def cmp99SourceGeneratedSmoothBasicAdjointFactorNormBound
    (P : CMP95SourceSmoothPartitionProfile)
    (M depth : ℕ) (spacing epsilon : ℝ) : ℝ :=
  cmp99SourceGeneratedSmoothFineBasicFactorNormBound
      P M depth spacing epsilon *
    cmp99SourceGeneratedWeightedAdjointNormBound M depth

namespace CMP99SourceDependentOmegaGeometry

set_option maxRecDepth 3000
set_option maxHeartbeats 6000000

/-- Literal smooth realization of `K(h'_Pi) G'_Pi h'_Pi` on the fine
regional carrier at one Section C scale. -/
noncomputable def generatedCMP95SourceCenteredSmoothFineSectionCBasicFactor
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
  let center := cmp99SourceGeneratedSmoothCutoffCenter M Q depth cell
  let h := fun x : ActiveGaugeRegion.Site
      (cmp99IteratedLiftActiveRegion (M := M) Omega (depth + 1)) =>
    P.tensorCutoff (cmp99SourceGeneratedSmoothCutoffScale M depth)
      (fun _ => 0) (finTorusDistanceCoordinates center x.1)
  let H := finitePiLpScalarMultiplier (g := SUNLieCoord Nc) h
  let Precision := cmp99SourceGeneratedPhysicalPrecision
    (show 2 ≤ 4 by norm_num) hM Omega depth spacing epsilon background budget
      fineSmall
  let G := cmp99SourceGeneratedPhysicalGreen
    (show 2 ≤ 4 by norm_num) hM Omega depth hspacing background budget
      fineSmall hsmall
  exact (finitePiLpScalarCommutator h Precision).comp (G.comp H)

/-- Exact source identity `K(h) G h = Delta' [G,h] h`.  In particular, the
smooth realization above is not merely bounded by a convenient surrogate. -/
theorem generatedCMP95SourceCenteredSmoothFineSectionCBasicFactor_eq_source
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
    let Omega := D.operatorCoarseRegion hpi5 s
    let center := cmp99SourceGeneratedSmoothCutoffCenter M Q depth cell
    let h := fun x : ActiveGaugeRegion.Site
        (cmp99IteratedLiftActiveRegion (M := M) Omega (depth + 1)) =>
      P.tensorCutoff (cmp99SourceGeneratedSmoothCutoffScale M depth)
        (fun _ => 0) (finTorusDistanceCoordinates center x.1)
    let H := finitePiLpScalarMultiplier (g := SUNLieCoord Nc) h
    let Precision := cmp99SourceGeneratedPhysicalPrecision
      (show 2 ≤ 4 by norm_num) hM Omega depth spacing epsilon background budget
        fineSmall
    let G := cmp99SourceGeneratedPhysicalGreen
      (show 2 ≤ 4 by norm_num) hM Omega depth hspacing background budget
        fineSmall hsmall
    D.generatedCMP95SourceCenteredSmoothFineSectionCBasicFactor P hpi5 s hM
        depth hspacing background budget fineSmall hsmall =
      Precision.comp
        ((finitePiLpOperatorScalarCommutator G h).comp H) := by
  dsimp only
  let Omega := D.operatorCoarseRegion hpi5 s
  let center := cmp99SourceGeneratedSmoothCutoffCenter M Q depth cell
  let h := fun x : ActiveGaugeRegion.Site
      (cmp99IteratedLiftActiveRegion (M := M) Omega (depth + 1)) =>
    P.tensorCutoff (cmp99SourceGeneratedSmoothCutoffScale M depth)
      (fun _ => 0) (finTorusDistanceCoordinates center x.1)
  let H := finitePiLpScalarMultiplier (g := SUNLieCoord Nc) h
  let Precision := cmp99SourceGeneratedPhysicalPrecision
    (show 2 ≤ 4 by norm_num) hM Omega depth spacing epsilon background budget
      fineSmall
  let G := cmp99SourceGeneratedPhysicalGreen
    (show 2 ≤ 4 by norm_num) hM Omega depth hspacing background budget
      fineSmall hsmall
  have hPG : Precision.comp G = ContinuousLinearMap.id ℝ _ := by
    exact cmp99SourceGeneratedPhysicalPrecision_comp_green
      (show 2 ≤ 4 by norm_num) hM Omega depth hspacing background budget
        fineSmall hsmall
  have hPG_apply : ∀ y, Precision (G y) = y := by
    intro y
    have := congrArg (fun T => T y) hPG
    simpa using this
  unfold generatedCMP95SourceCenteredSmoothFineSectionCBasicFactor
  change (finitePiLpScalarCommutator h Precision).comp (G.comp H) =
    Precision.comp ((finitePiLpOperatorScalarCommutator G h).comp H)
  ext x
  simp only [ContinuousLinearMap.comp_apply, finitePiLpScalarCommutator,
    finitePiLpOperatorScalarCommutator, ContinuousLinearMap.sub_apply]
  rw [hPG_apply, map_sub, hPG_apply]

/-- The smooth basic factor has a volume-independent norm whose explicit
constant retains the CMP95 derivative-scale gain. -/
theorem norm_generatedCMP95SourceCenteredSmoothFineSectionCBasicFactor_le
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
    ‖D.generatedCMP95SourceCenteredSmoothFineSectionCBasicFactor P hpi5 s hM
      depth hspacing background budget fineSmall hsmall‖ ≤
      cmp99SourceGeneratedSmoothFineBasicFactorNormBound
        P M depth spacing epsilon := by
  let Omega := D.operatorCoarseRegion hpi5 s
  let center := cmp99SourceGeneratedSmoothCutoffCenter M Q depth cell
  let h := fun x : ActiveGaugeRegion.Site
      (cmp99IteratedLiftActiveRegion (M := M) Omega (depth + 1)) =>
    P.tensorCutoff (cmp99SourceGeneratedSmoothCutoffScale M depth)
      (fun _ => 0) (finTorusDistanceCoordinates center x.1)
  let H := finitePiLpScalarMultiplier (g := SUNLieCoord Nc) h
  let Precision := cmp99SourceGeneratedPhysicalPrecision
    (show 2 ≤ 4 by norm_num) hM Omega depth spacing epsilon background budget
      fineSmall
  let C := cmp99SourceGeneratedPhysicalGreenSmoothCommutator
    P Omega (fun _ => 0) (fun x => finTorusDistanceCoordinates center x.1)
      hM hspacing background budget fineSmall hsmall
  let APrecision := cmp99SourceGeneratedPhysicalPrecisionUpperBound
    4 M (depth + 1) spacing epsilon
  let AC := cmp99SourceGeneratedSmoothGreenLinearCommutatorNormBound
    P M depth spacing epsilon
  have hPrecision : ‖Precision‖ ≤ APrecision := by
    simpa [Precision, APrecision] using
      norm_cmp99SourceGeneratedPhysicalPrecision_le
        (show 2 ≤ 4 by norm_num) hM Omega depth hspacing background budget
          fineSmall
  have hC : ‖C‖ ≤ AC := by
    simpa [C, AC,
      cmp99SourceGeneratedSmoothGreenLinearCommutatorNormBound] using
      norm_cmp99SourceGeneratedPhysicalGreenSmoothCommutator_le
        P Omega (fun _ => 0)
          (fun x => finTorusDistanceCoordinates center x.1)
          (fun target source =>
            sum_norm_finTorusDistanceCoordinates_sub_le_four_finBoxDist
              center target.1 source.1)
          hM hspacing background budget fineSmall hsmall
  have hH : ‖H‖ ≤ 1 :=
    norm_finitePiLpScalarMultiplier_le_one _
      (fun x => P.norm_tensorCutoff_le_one _ _ _)
  have hAPrecision : 0 ≤ APrecision :=
    (norm_nonneg Precision).trans hPrecision
  have hAC : 0 ≤ AC := (norm_nonneg C).trans hC
  rw [D.generatedCMP95SourceCenteredSmoothFineSectionCBasicFactor_eq_source
    P hpi5 s hM depth hspacing background budget fineSmall hsmall]
  calc
    ‖Precision.comp (C.comp H)‖ ≤ ‖Precision‖ * ‖C.comp H‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ APrecision * (AC * 1) := by
      gcongr
      exact (ContinuousLinearMap.opNorm_comp_le C H).trans
        (mul_le_mul hC hH (norm_nonneg H) hAC)
    _ = cmp99SourceGeneratedSmoothFineBasicFactorNormBound
        P M depth spacing epsilon := by
      simp only [mul_one]
      rfl

/-- Literal smooth realization of the mixed-scale factor
`K(h'_Pi) G'_Pi h'_Pi Q'^*` singled out on CMP99 printed p. 413. -/
noncomputable def generatedCMP95SourceCenteredSmoothSectionCBasicAdjointFactor
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
  let regions := cmp99SourceIteratedLiftActiveRegionChain (M := M)
    Omega (depth + 1)
  let T := regions.weightedQprimeTower (show 2 ≤ 4 by norm_num) hM
    (matrixSUNAdjointModel Nc) spacing epsilon background
    budget.toRadiusChain fineSmall
  let Basic :=
    D.generatedCMP95SourceCenteredSmoothFineSectionCBasicFactor P hpi5 s hM
      depth hspacing background budget fineSmall hsmall
  exact Basic.comp T.weightedAdjoint

/-- The mixed-scale definition unfolds to the precise printed composition;
no equality transport or ambient zero extension is inserted. -/
theorem generatedCMP95SourceCenteredSmoothSectionCBasicAdjointFactor_eq_source
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
    let Omega := D.operatorCoarseRegion hpi5 s
    let regions := cmp99SourceIteratedLiftActiveRegionChain (M := M)
      Omega (depth + 1)
    let T := regions.weightedQprimeTower (show 2 ≤ 4 by norm_num) hM
      (matrixSUNAdjointModel Nc) spacing epsilon background
      budget.toRadiusChain fineSmall
    D.generatedCMP95SourceCenteredSmoothSectionCBasicAdjointFactor P hpi5 s
        hM depth hspacing background budget fineSmall hsmall =
      (D.generatedCMP95SourceCenteredSmoothFineSectionCBasicFactor P hpi5 s
        hM depth hspacing background budget fineSmall hsmall).comp
          T.weightedAdjoint := by
  rfl

/-- The p. 413 mixed-scale factor retains the same smooth commutator gain,
with only the already proved weighted-adjoint cost added. -/
theorem norm_generatedCMP95SourceCenteredSmoothSectionCBasicAdjointFactor_le
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
    ‖D.generatedCMP95SourceCenteredSmoothSectionCBasicAdjointFactor P hpi5 s
      hM depth hspacing background budget fineSmall hsmall‖ ≤
      cmp99SourceGeneratedSmoothBasicAdjointFactorNormBound
        P M depth spacing epsilon := by
  let Omega := D.operatorCoarseRegion hpi5 s
  let regions := cmp99SourceIteratedLiftActiveRegionChain (M := M)
    Omega (depth + 1)
  let T := regions.weightedQprimeTower (show 2 ≤ 4 by norm_num) hM
    (matrixSUNAdjointModel Nc) spacing epsilon background
    budget.toRadiusChain fineSmall
  let Basic :=
    D.generatedCMP95SourceCenteredSmoothFineSectionCBasicFactor P hpi5 s hM
      depth hspacing background budget fineSmall hsmall
  let ABasic := cmp99SourceGeneratedSmoothFineBasicFactorNormBound
    P M depth spacing epsilon
  let W := cmp99SourceGeneratedWeightedAdjointNormBound M depth
  have hBasic : ‖Basic‖ ≤ ABasic :=
    D.norm_generatedCMP95SourceCenteredSmoothFineSectionCBasicFactor_le P
      hpi5 s hM depth hspacing background budget fineSmall hsmall
  have hW : ‖T.weightedAdjoint‖ ≤ W :=
    D.norm_generatedWeightedAdjoint_le hpi5 s hM depth hspacing background
      budget fineSmall
  have hABasic : 0 ≤ ABasic := (norm_nonneg Basic).trans hBasic
  unfold generatedCMP95SourceCenteredSmoothSectionCBasicAdjointFactor
  change ‖Basic.comp T.weightedAdjoint‖ ≤ _
  calc
    ‖Basic.comp T.weightedAdjoint‖ ≤ ‖Basic‖ * ‖T.weightedAdjoint‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ABasic * W :=
      mul_le_mul hBasic hW (norm_nonneg T.weightedAdjoint) hABasic
    _ = cmp99SourceGeneratedSmoothBasicAdjointFactorNormBound
        P M depth spacing epsilon := rfl

end CMP99SourceDependentOmegaGeometry

end
end YangMills.RG
