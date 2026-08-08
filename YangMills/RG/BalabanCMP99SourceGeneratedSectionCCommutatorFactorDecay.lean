/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceGeneratedSectionCSmoothCommutatorFactor
import YangMills.RG.BalabanCMP99SourceOperatorCoarseRegionDiameter
import YangMills.RG.FinitePiLpTypedWeightedRowKernel

/-!
# Fixed-rate decay of the printed CMP99 commutator species

The exact p. 412 commutator factor is supported on one generated operator
region inside `tilde Pi^5`.  Its source-specific norm budget therefore yields
an exponential kernel certificate and a weighted-row certificate without an
ambient-volume cardinality.
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

/-- Explicit fixed-rate weighted-row amplitude of the p. 412 commutator
factor. -/
noncomputable def
    cmp99SourceGeneratedPhysicalCoarseCommutatorWeightedRowAmplitude
    (M depth : ℕ) (spacing epsilon rate : ℝ) : ℝ :=
  cmp99SourceGeneratedPhysicalCoarseRightFactorNormBound
      M depth spacing epsilon *
    Real.exp ((2 * rate) * ((1 + 2 * 5 : ℕ) : ℝ)) * 20736

/-- Fixed-rate weighted-row amplitude for the source-centred smooth p. 412
species.  Unlike the older block-constant realization, this amplitude retains
the derivative-scale gain inherited from CMP95 (1.118). -/
noncomputable def
    cmp99SourceGeneratedCMP95SmoothCommutatorWeightedRowAmplitude
    (P : CMP95SourceSmoothPartitionProfile)
    (M depth : ℕ) (spacing epsilon rate : ℝ) : ℝ :=
  cmp99SourceGeneratedSmoothSectionCFactorNormBound
      P M depth spacing epsilon *
    Real.exp ((2 * rate) * ((1 + 2 * 5 : ℕ) : ℝ)) * 20736

/-- An operator norm and a uniform diameter give exponential decay on a
finite typed carrier.  Keeping this lemma operator-generic prevents the
source-generated dependent tower from being normalized inside the kernel
argument. -/
private theorem exponentialKernelBound_of_norm_of_diameter
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
set_option maxHeartbeats 100000

/-- Pointwise fixed-rate decay of the exact same-scale commutator species. -/
theorem generatedPhysicalCoarseSectionCCommutatorFactorCoordinates_exponential
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
    let F : FinitePiLpField (ActiveGaugeRegion.Site
          (D.operatorCoarseRegion hpi5 s)) (SUNLieCoord Nc) →L[ℝ]
        FinitePiLpField (ActiveGaugeRegion.Site
          (D.operatorCoarseRegion hpi5 s)) (SUNLieCoord Nc) :=
      (D.generatedPhysicalCoarseSectionCCommutatorFactorCertificate P hpi5 s
        hM depth (spacing := spacing) (epsilon := epsilon) hspacing background
        budget fineSmall hsmall).operator
    FinitePiLpTypedExponentialKernelBound
      (ι := ActiveGaugeRegion.Site (D.operatorCoarseRegion hpi5 s))
      (κ := ActiveGaugeRegion.Site (D.operatorCoarseRegion hpi5 s))
      (g := SUNLieCoord Nc)
      F
      (activeGaugeRegionSiteFinBoxDist (D.operatorCoarseRegion hpi5 s))
      (cmp99SourceGeneratedPhysicalCoarseRightFactorNormBound
          M depth spacing epsilon *
        Real.exp (rate * ((1 + 2 * 5 : ℕ) : ℝ))) rate := by
  dsimp only
  let A := cmp99SourceGeneratedPhysicalCoarseRightFactorNormBound
    M depth spacing epsilon
  have hA : 0 ≤ A := by
    dsimp [A, cmp99SourceGeneratedPhysicalCoarseRightFactorNormBound]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (by norm_num) (sq_nonneg _))
        (pow_nonneg (Nat.cast_nonneg M) _))
      (inv_nonneg.mpr (inv_nonneg.mpr (sq_nonneg _)))
  have hdiam : ∀ target source,
      activeGaugeRegionSiteFinBoxDist (D.operatorCoarseRegion hpi5 s)
        target source ≤ 1 + 2 * 5 :=
    fun target source =>
      D.operatorCoarseRegion_siteFinBoxDist_le_pi5 hpi5 s target source
  have hnorm :
      ‖(D.generatedPhysicalCoarseSectionCCommutatorFactorCertificate P hpi5 s
        hM depth (spacing := spacing) (epsilon := epsilon) hspacing background
        budget fineSmall hsmall).operator‖ ≤ A := by
    dsimp only [A]
    exact (D.generatedPhysicalCoarseSectionCCommutatorFactorCertificate P
      hpi5 s hM depth (spacing := spacing) (epsilon := epsilon) hspacing
      background budget fineSmall hsmall).norm_le
  have hresult := exponentialKernelBound_of_norm_of_diameter
    ((D.generatedPhysicalCoarseSectionCCommutatorFactorCertificate P hpi5 s
      hM depth (spacing := spacing) (epsilon := epsilon) hspacing background
      budget fineSmall hsmall).operator)
    (activeGaugeRegionSiteFinBoxDist (D.operatorCoarseRegion hpi5 s))
    (1 + 2 * 5) hA hrate hdiam hnorm
  exact hresult

/-- Fixed-rate weighted rows for the exact p. 412 commutator factor. -/
theorem generatedPhysicalCoarseSectionCCommutatorFactorCoordinates_weightedRow
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
    let F : FinitePiLpField (ActiveGaugeRegion.Site
          (D.operatorCoarseRegion hpi5 s)) (SUNLieCoord Nc) →L[ℝ]
        FinitePiLpField (ActiveGaugeRegion.Site
          (D.operatorCoarseRegion hpi5 s)) (SUNLieCoord Nc) :=
      (D.generatedPhysicalCoarseSectionCCommutatorFactorCertificate P hpi5 s
        hM depth (spacing := spacing) (epsilon := epsilon) hspacing background
        budget fineSmall hsmall).operator
    FinitePiLpTypedWeightedRowKernelBound
      (ι := ActiveGaugeRegion.Site (D.operatorCoarseRegion hpi5 s))
      (κ := ActiveGaugeRegion.Site (D.operatorCoarseRegion hpi5 s))
      (g := SUNLieCoord Nc)
      F
      (activeGaugeRegionSiteFinBoxDist (D.operatorCoarseRegion hpi5 s))
      (cmp99SourceGeneratedPhysicalCoarseCommutatorWeightedRowAmplitude
        M depth spacing epsilon rate) rate := by
  dsimp only
  have hpoint : FinitePiLpTypedExponentialKernelBound
      (ι := ActiveGaugeRegion.Site (D.operatorCoarseRegion hpi5 s))
      (κ := ActiveGaugeRegion.Site (D.operatorCoarseRegion hpi5 s))
      (g := SUNLieCoord Nc)
      ((D.generatedPhysicalCoarseSectionCCommutatorFactorCertificate P hpi5 s
        hM depth (spacing := spacing) (epsilon := epsilon) hspacing background
        budget fineSmall hsmall).operator)
      (activeGaugeRegionSiteFinBoxDist (D.operatorCoarseRegion hpi5 s))
      (cmp99SourceGeneratedPhysicalCoarseRightFactorNormBound
          M depth spacing epsilon *
        Real.exp ((2 * rate) * ((1 + 2 * 5 : ℕ) : ℝ))) (2 * rate) :=
    D.generatedPhysicalCoarseSectionCCommutatorFactorCoordinates_exponential
      P hpi5 s hM depth (spacing := spacing) (epsilon := epsilon)
      (rate := 2 * rate) hspacing (by positivity) background budget fineSmall
      hsmall
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
    ((D.generatedPhysicalCoarseSectionCCommutatorFactorCertificate P hpi5 s
      hM depth (spacing := spacing) (epsilon := epsilon) hspacing background
      budget fineSmall hsmall).operator)
    (activeGaugeRegionSiteFinBoxDist (D.operatorCoarseRegion hpi5 s))
    hrate.le (by norm_num : (0 : ℝ) ≤ 20736) hpoint hsum
  simpa [
    cmp99SourceGeneratedPhysicalCoarseCommutatorWeightedRowAmplitude] using
      hrow

/-- Pointwise fixed-rate decay of the complete source-centred smooth p. 412
species generated from one CMP95 profile.  The amplitude keeps the
`M0^-1` commutator gain and the spatial rate is arbitrary and fixed. -/
theorem
    generatedCMP95SourceCenteredSectionCCommutatorFactorCoordinates_exponential
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
      (D.generatedCMP95SourceCenteredSectionCCommutatorFactorCertificate P
        hpi5 s hM depth (spacing := spacing) (epsilon := epsilon) hspacing
        background budget fineSmall hsmall).operator
    FinitePiLpTypedExponentialKernelBound
      (ι := ActiveGaugeRegion.Site (D.operatorCoarseRegion hpi5 s))
      (κ := ActiveGaugeRegion.Site (D.operatorCoarseRegion hpi5 s))
      (g := SUNLieCoord Nc)
      F
      (activeGaugeRegionSiteFinBoxDist (D.operatorCoarseRegion hpi5 s))
      (cmp99SourceGeneratedSmoothSectionCFactorNormBound
          P M depth spacing epsilon *
        Real.exp (rate * ((1 + 2 * 5 : ℕ) : ℝ))) rate := by
  dsimp only
  let Cert :=
    D.generatedCMP95SourceCenteredSectionCCommutatorFactorCertificate P
      hpi5 s hM depth (spacing := spacing) (epsilon := epsilon) hspacing
      background budget fineSmall hsmall
  let A := cmp99SourceGeneratedSmoothSectionCFactorNormBound
    P M depth spacing epsilon
  have hnorm : ‖Cert.operator‖ ≤ A := Cert.norm_le
  have hA : 0 ≤ A := (norm_nonneg Cert.operator).trans hnorm
  have hdiam : ∀ target source,
      activeGaugeRegionSiteFinBoxDist (D.operatorCoarseRegion hpi5 s)
        target source ≤ 1 + 2 * 5 :=
    fun target source =>
      D.operatorCoarseRegion_siteFinBoxDist_le_pi5 hpi5 s target source
  exact exponentialKernelBound_of_norm_of_diameter Cert.operator
    (activeGaugeRegionSiteFinBoxDist (D.operatorCoarseRegion hpi5 s))
    (1 + 2 * 5) hA hrate hdiam hnorm

/-- Fixed-rate weighted rows for the complete source-centred smooth p. 412
species.  Both the cutoff family and its commutator derivative scale are
generated from the same CMP95 profile. -/
theorem
    generatedCMP95SourceCenteredSectionCCommutatorFactorCoordinates_weightedRow
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
      (D.generatedCMP95SourceCenteredSectionCCommutatorFactorCertificate P
        hpi5 s hM depth (spacing := spacing) (epsilon := epsilon) hspacing
        background budget fineSmall hsmall).operator
    FinitePiLpTypedWeightedRowKernelBound
      (ι := ActiveGaugeRegion.Site (D.operatorCoarseRegion hpi5 s))
      (κ := ActiveGaugeRegion.Site (D.operatorCoarseRegion hpi5 s))
      (g := SUNLieCoord Nc)
      F
      (activeGaugeRegionSiteFinBoxDist (D.operatorCoarseRegion hpi5 s))
      (cmp99SourceGeneratedCMP95SmoothCommutatorWeightedRowAmplitude
        P M depth spacing epsilon rate) rate := by
  dsimp only
  let Cert :=
    D.generatedCMP95SourceCenteredSectionCCommutatorFactorCertificate P
      hpi5 s hM depth (spacing := spacing) (epsilon := epsilon) hspacing
      background budget fineSmall hsmall
  have hpoint : FinitePiLpTypedExponentialKernelBound
      (ι := ActiveGaugeRegion.Site (D.operatorCoarseRegion hpi5 s))
      (κ := ActiveGaugeRegion.Site (D.operatorCoarseRegion hpi5 s))
      (g := SUNLieCoord Nc) Cert.operator
      (activeGaugeRegionSiteFinBoxDist (D.operatorCoarseRegion hpi5 s))
      (cmp99SourceGeneratedSmoothSectionCFactorNormBound
          P M depth spacing epsilon *
        Real.exp ((2 * rate) * ((1 + 2 * 5 : ℕ) : ℝ)))
      (2 * rate) :=
    D.generatedCMP95SourceCenteredSectionCCommutatorFactorCoordinates_exponential
      P hpi5 s hM depth (spacing := spacing) (epsilon := epsilon)
      (rate := 2 * rate) hspacing (by positivity) background budget fineSmall
      hsmall
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
    Cert.operator
    (activeGaugeRegionSiteFinBoxDist (D.operatorCoarseRegion hpi5 s))
    hrate.le (by norm_num : (0 : ℝ) ≤ 20736) hpoint hsum
  simpa [cmp99SourceGeneratedCMP95SmoothCommutatorWeightedRowAmplitude] using
    hrow

end CMP99SourceDependentOmegaGeometry

end
end YangMills.RG
