/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP95PeriodicSquarePartition
import YangMills.RG.BalabanCMP99SourceGeneratedSectionCCommutatorFactorDecay

/-!
# The literal CMP99 Section C head factor

CMP99 printed p. 413 starts the generalized regional expansion with

`R'_0(Pi) = h_Pi C_Pi h_Pi`.

This file isolates that head on the generated physical coarse coordinates.
The cutoff is not a caller-supplied contraction: it is the exact periodic
square partition generated from the CMP95 (1.118) profile.  The common
`tilde Pi^5` envelope then gives a fixed-rate weighted row with no ambient-
volume factor.
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

/-- Fixed-rate row amplitude of the literal head `h_Pi C_Pi h_Pi`.
The constants `11` and `20736` are respectively the diameter and carrier
budget of the source `tilde Pi^5` envelope. -/
noncomputable def cmp99SourceGeneratedSectionCHeadWeightedRowAmplitude
    (M depth : ℕ) (spacing epsilon rate : ℝ) : ℝ :=
  cmp99SourceGeneratedPhysicalCoarseCovarianceNormBound
      M depth spacing epsilon *
    Real.exp ((2 * rate) * ((1 + 2 * 5 : ℕ) : ℝ)) * 20736

/-- A norm bound and the source-region diameter give pointwise exponential
decay.  The operator is kept abstract here so dependent tower definitions do
not unfold inside the kernel proof. -/
private theorem sectionCHeadExponentialKernelBound_of_norm_of_diameter
    {ι g : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup g] [NormedSpace ℝ g]
    (F : FinitePiLpField ι g →L[ℝ] FinitePiLpField ι g)
    (sourceDist : ι → ι → ℕ) (R : ℕ) {A rate : ℝ}
    (hA : 0 ≤ A) (hrate : 0 < rate)
    (hdiam : ∀ target source, sourceDist target source ≤ R)
    (hnorm : ‖F‖ ≤ A) :
    FinitePiLpTypedExponentialKernelBound F sourceDist
      (A * Real.exp (rate * (R : ℝ))) rate := by
  have hrange : FinitePiLpTypedFiniteRange F sourceDist R := by
    intro source target v hfar
    have hnear := hdiam target source
    omega
  have hkernel : FinitePiLpTypedKernelBound F (fun _ _ => A) := by
    have hentry := finitePiLpTypedKernelBound_const_opNorm F
    intro source target v
    exact (hentry source target v).trans
      (mul_le_mul_of_nonneg_right hnorm (norm_nonneg v))
  exact finitePiLpTypedExponentialKernelBound_of_finiteRange
    hA hrate F hrange hkernel

namespace CMP99SourceDependentOmegaGeometry

set_option maxRecDepth 3000
set_option maxHeartbeats 500000

/-- Literal source head `R'_0(Pi) = h_Pi C_Pi h_Pi`, with `h_Pi`
generated from the CMP95 smooth partition profile. -/
noncomputable def generatedSectionCSourceHeadFactorCoordinates
    (D : CMP99SourceDependentOmegaGeometry
      (FinBox 4 (2 * Q)) j ScaleSite Scaled
      (cmp99SourceTildePiLargeBlocks cell 3)
      (cmp99SourceTildePiLargeBlocks cell 4) dist gap)
    (P : CMP99SourceSquarePartition Q)
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
    FinitePiLpField (ActiveGaugeRegion.Site
        (D.operatorCoarseRegion hpi5 s)) (SUNLieCoord Nc) →L[ℝ]
      FinitePiLpField (ActiveGaugeRegion.Site
        (D.operatorCoarseRegion hpi5 s)) (SUNLieCoord Nc) :=
  let H := finitePiLpScalarMultiplier (g := SUNLieCoord Nc)
    (fun x : ActiveGaugeRegion.Site (D.operatorCoarseRegion hpi5 s) =>
      P.value cell x.1)
  let C := D.generatedPhysicalCoarseCovarianceCoordinates hpi5 s hM depth
    hspacing background budget fineSmall hsmall
  H.comp (C.comp H)

/-- The two literal source cutoffs do not enlarge the covariance norm. -/
theorem norm_generatedSectionCSourceHeadFactorCoordinates_le
    (D : CMP99SourceDependentOmegaGeometry
      (FinBox 4 (2 * Q)) j ScaleSite Scaled
      (cmp99SourceTildePiLargeBlocks cell 3)
      (cmp99SourceTildePiLargeBlocks cell 4) dist gap)
    (P : CMP99SourceSquarePartition Q)
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
    ‖D.generatedSectionCSourceHeadFactorCoordinates P hpi5 s hM depth
      hspacing background budget fineSmall hsmall‖ ≤
      cmp99SourceGeneratedPhysicalCoarseCovarianceNormBound
        M depth spacing epsilon := by
  let H := finitePiLpScalarMultiplier (g := SUNLieCoord Nc)
    (fun x : ActiveGaugeRegion.Site (D.operatorCoarseRegion hpi5 s) =>
      P.value cell x.1)
  let C := D.generatedPhysicalCoarseCovarianceCoordinates hpi5 s hM depth
    hspacing background budget fineSmall hsmall
  have hH : ‖H‖ ≤ 1 :=
    norm_finitePiLpScalarMultiplier_le_one _
      (fun x => P.norm_value_le_one cell x.1)
  have hC : ‖C‖ ≤
      cmp99SourceGeneratedPhysicalCoarseCovarianceNormBound
        M depth spacing epsilon :=
    D.norm_generatedPhysicalCoarseCovarianceCoordinates_le hpi5 s hM depth
      hspacing background budget fineSmall hsmall
  have hCnonneg : 0 ≤
      cmp99SourceGeneratedPhysicalCoarseCovarianceNormBound
        M depth spacing epsilon := (norm_nonneg C).trans hC
  have hCH : ‖C.comp H‖ ≤
      cmp99SourceGeneratedPhysicalCoarseCovarianceNormBound
        M depth spacing epsilon := by
    calc
      ‖C.comp H‖ ≤ ‖C‖ * ‖H‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ _ * 1 :=
        mul_le_mul hC hH (norm_nonneg H) hCnonneg
      _ = _ := mul_one _
  change ‖H.comp (C.comp H)‖ ≤ _
  calc
    ‖H.comp (C.comp H)‖ ≤ ‖H‖ * ‖C.comp H‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * cmp99SourceGeneratedPhysicalCoarseCovarianceNormBound
        M depth spacing epsilon :=
      mul_le_mul hH hCH (norm_nonneg _) zero_le_one
    _ = _ := one_mul _

/-- The literal head packaged with its volume-independent norm certificate.
This keeps later kernel arguments from normalizing the generated tower. -/
noncomputable def generatedSectionCSourceHeadFactorCertificate
    (D : CMP99SourceDependentOmegaGeometry
      (FinBox 4 (2 * Q)) j ScaleSite Scaled
      (cmp99SourceTildePiLargeBlocks cell 3)
      (cmp99SourceTildePiLargeBlocks cell 4) dist gap)
    (P : CMP99SourceSquarePartition Q)
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
    CMP99SectionCTypedEndomorphismWithNorm
      (ActiveGaugeRegion.Site (D.operatorCoarseRegion hpi5 s))
      (SUNLieCoord Nc)
      (cmp99SourceGeneratedPhysicalCoarseCovarianceNormBound
        M depth spacing epsilon) where
  operator := D.generatedSectionCSourceHeadFactorCoordinates P hpi5 s hM
    depth hspacing background budget fineSmall hsmall
  norm_le := D.norm_generatedSectionCSourceHeadFactorCoordinates_le P hpi5 s
    hM depth hspacing background budget fineSmall hsmall

/-- Pointwise fixed-rate decay of the literal source head.  Since its whole
physical carrier lies in `tilde Pi^5`, the already proved norm bound implies
an exponential kernel bound at any positive rate. -/
theorem generatedSectionCSourceHeadFactorCoordinates_exponential
    (D : CMP99SourceDependentOmegaGeometry
      (FinBox 4 (2 * Q)) j ScaleSite Scaled
      (cmp99SourceTildePiLargeBlocks cell 3)
      (cmp99SourceTildePiLargeBlocks cell 4) dist gap)
    (P : CMP99SourceSquarePartition Q)
    (hpi5 : D.fineRegion (cmp99OmegaZeroIndex j) ⊆
      cmp99SourceTildePiLargeBlocks cell 5)
    (s : Fin (j + 2)) (hM : 2 ≤ M) (depth : ℕ)
    {spacing epsilon rate : ℝ} (hspacing : 0 < spacing) (hrate : 0 < rate)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 M Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff 4 M (depth + 1)
      spacing epsilon < 1) :
    FinitePiLpTypedExponentialKernelBound
      (D.generatedSectionCSourceHeadFactorCertificate P hpi5 s hM depth
        hspacing background budget fineSmall hsmall).operator
      (activeGaugeRegionSiteFinBoxDist (D.operatorCoarseRegion hpi5 s))
      (cmp99SourceGeneratedPhysicalCoarseCovarianceNormBound
          M depth spacing epsilon *
        Real.exp (rate * ((1 + 2 * 5 : ℕ) : ℝ))) rate := by
  let F := (D.generatedSectionCSourceHeadFactorCertificate P hpi5 s hM
    depth hspacing background budget fineSmall hsmall).operator
  let A := cmp99SourceGeneratedPhysicalCoarseCovarianceNormBound
    M depth spacing epsilon
  have hA : 0 ≤ A := by
    exact (norm_nonneg F).trans
      (D.generatedSectionCSourceHeadFactorCertificate P hpi5 s hM depth
        hspacing background budget fineSmall hsmall).norm_le
  have hdiam : ∀ left right,
      activeGaugeRegionSiteFinBoxDist (D.operatorCoarseRegion hpi5 s)
        left right ≤ 1 + 2 * 5 :=
    D.operatorCoarseRegion_siteFinBoxDist_le_pi5 hpi5 s
  have hnorm : ‖F‖ ≤ A :=
    (D.generatedSectionCSourceHeadFactorCertificate P hpi5 s hM depth
      hspacing background budget fineSmall hsmall).norm_le
  exact sectionCHeadExponentialKernelBound_of_norm_of_diameter F
    (activeGaugeRegionSiteFinBoxDist (D.operatorCoarseRegion hpi5 s))
    (1 + 2 * 5) hA hrate hdiam hnorm

/-- Fixed-rate weighted row of the literal head.  The amplitude depends only
on the source coercivity parameters and the fixed `tilde Pi^5` envelope. -/
theorem generatedSectionCSourceHeadFactorCoordinates_weightedRow
    (D : CMP99SourceDependentOmegaGeometry
      (FinBox 4 (2 * Q)) j ScaleSite Scaled
      (cmp99SourceTildePiLargeBlocks cell 3)
      (cmp99SourceTildePiLargeBlocks cell 4) dist gap)
    (P : CMP99SourceSquarePartition Q)
    (hpi5 : D.fineRegion (cmp99OmegaZeroIndex j) ⊆
      cmp99SourceTildePiLargeBlocks cell 5)
    (s : Fin (j + 2)) (hM : 2 ≤ M) (depth : ℕ)
    {spacing epsilon rate : ℝ} (hspacing : 0 < spacing) (hrate : 0 < rate)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 M Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff 4 M (depth + 1)
      spacing epsilon < 1) :
    FinitePiLpTypedWeightedRowKernelBound
      (D.generatedSectionCSourceHeadFactorCertificate P hpi5 s hM depth
        hspacing background budget fineSmall hsmall).operator
      (activeGaugeRegionSiteFinBoxDist (D.operatorCoarseRegion hpi5 s))
      (cmp99SourceGeneratedSectionCHeadWeightedRowAmplitude
        M depth spacing epsilon rate) rate := by
  have hpoint :=
    D.generatedSectionCSourceHeadFactorCoordinates_exponential P hpi5 s
      hM depth hspacing (rate := 2 * rate) (by positivity) background budget
      fineSmall hsmall
  have hcard : Fintype.card (ActiveGaugeRegion.Site
      (D.operatorCoarseRegion hpi5 s)) ≤ 20736 :=
    D.operatorCoarseRegion_site_card_le_pi5 hpi5 s
  have hsum : ∀ source,
      ∑ target : ActiveGaugeRegion.Site (D.operatorCoarseRegion hpi5 s),
        Real.exp (-(((2 * rate) - rate) *
          (activeGaugeRegionSiteFinBoxDist
            (D.operatorCoarseRegion hpi5 s) target source : ℝ))) ≤
          (20736 : ℝ) := by
    intro source
    calc
      ∑ target, Real.exp (-(((2 * rate) - rate) *
          (activeGaugeRegionSiteFinBoxDist
            (D.operatorCoarseRegion hpi5 s) target source : ℝ))) ≤
          ∑ _target, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro target _
        rw [Real.exp_le_one_iff]
        have hdist : 0 ≤ (activeGaugeRegionSiteFinBoxDist
          (D.operatorCoarseRegion hpi5 s) target source : ℝ) := by positivity
        nlinarith
      _ = (Fintype.card (ActiveGaugeRegion.Site
          (D.operatorCoarseRegion hpi5 s)) : ℝ) := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
      _ ≤ 20736 := by exact_mod_cast hcard
  have hrow := finitePiLpTypedWeightedRowKernelBound_of_exponential
    (D.generatedSectionCSourceHeadFactorCertificate P hpi5 s hM depth
      hspacing background budget fineSmall hsmall).operator
    (activeGaugeRegionSiteFinBoxDist (D.operatorCoarseRegion hpi5 s))
    hrate.le (by norm_num : (0 : ℝ) ≤ 20736) hpoint hsum
  simpa [cmp99SourceGeneratedSectionCHeadWeightedRowAmplitude] using hrow

/-- Source-faithful CMP95 specialization of the head.  The only partition
inserted here is the exact periodic partition generated from (1.118). -/
noncomputable def generatedCMP95SectionCSourceHeadFactorCoordinates
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
      spacing epsilon < 1) :=
  D.generatedSectionCSourceHeadFactorCoordinates
    (cmp95SourcePeriodicCoarseSquarePartition P Q) hpi5 s hM depth hspacing
      background budget fineSmall hsmall

/-- The CMP95-generated literal head inherits the source-partition weighted
row without any additional cutoff or estimate. -/
theorem generatedCMP95SectionCSourceHeadFactorCoordinates_weightedRow
    (D : CMP99SourceDependentOmegaGeometry
      (FinBox 4 (2 * Q)) j ScaleSite Scaled
      (cmp99SourceTildePiLargeBlocks cell 3)
      (cmp99SourceTildePiLargeBlocks cell 4) dist gap)
    (P : CMP95SourceSmoothPartitionProfile)
    (hpi5 : D.fineRegion (cmp99OmegaZeroIndex j) ⊆
      cmp99SourceTildePiLargeBlocks cell 5)
    (s : Fin (j + 2)) (hM : 2 ≤ M) (depth : ℕ)
    {spacing epsilon rate : ℝ} (hspacing : 0 < spacing) (hrate : 0 < rate)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 M Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff 4 M (depth + 1)
      spacing epsilon < 1) :
    let F : FinitePiLpField (ActiveGaugeRegion.Site
          (D.operatorCoarseRegion hpi5 s)) (SUNLieCoord Nc) →L[ℝ]
        FinitePiLpField (ActiveGaugeRegion.Site
          (D.operatorCoarseRegion hpi5 s)) (SUNLieCoord Nc) :=
      D.generatedCMP95SectionCSourceHeadFactorCoordinates P hpi5 s hM depth
        hspacing background budget fineSmall hsmall
    FinitePiLpTypedWeightedRowKernelBound
      F
      (activeGaugeRegionSiteFinBoxDist (D.operatorCoarseRegion hpi5 s))
      (cmp99SourceGeneratedSectionCHeadWeightedRowAmplitude
        M depth spacing epsilon rate) rate := by
  change FinitePiLpTypedWeightedRowKernelBound
    (D.generatedSectionCSourceHeadFactorCertificate
      (cmp95SourcePeriodicCoarseSquarePartition P Q) hpi5 s hM depth hspacing
        background budget fineSmall hsmall).operator
    (activeGaugeRegionSiteFinBoxDist (D.operatorCoarseRegion hpi5 s))
    (cmp99SourceGeneratedSectionCHeadWeightedRowAmplitude
      M depth spacing epsilon rate) rate
  exact D.generatedSectionCSourceHeadFactorCoordinates_weightedRow
    (cmp95SourcePeriodicCoarseSquarePartition P Q) hpi5 s hM depth hspacing
      hrate background budget fineSmall hsmall

end CMP99SourceDependentOmegaGeometry

end
end YangMills.RG
