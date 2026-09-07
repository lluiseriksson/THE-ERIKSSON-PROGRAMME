/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP95PeriodicSquarePartitionSupportCardinality
import YangMills.RG.BalabanCMP99SourceGeneratedSectionCHeadSupport

/-!
# Support-sharp weighted row for the CMP99 covariance head

The literal CMP99 p. 413 head is `h_Pi C_Pi h_Pi`.  The two source cutoffs
make every matrix entry vanish unless both endpoints lie in the exact
periodized support of CMP95 (1.118).  That support has at most `3^4 = 81`
large blocks.  This replaces the earlier crude `12^4 = 20736` count of the
whole `tilde Pi^5` regional carrier in the fixed-rate weighted-row bound.
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

/-- Support-sharp fixed-rate amplitude of the source-generated p. 413 head. -/
noncomputable def cmp99SourceGeneratedCMP95SectionCHeadWeightedRowAmplitude
    (M depth : ℕ) (spacing epsilon rate : ℝ) : ℝ :=
  cmp99SourceGeneratedPhysicalCoarseCovarianceNormBound
      M depth spacing epsilon *
    Real.exp (rate * ((1 + 2 * 5 : ℕ) : ℝ)) * 81

namespace CMP99SourceDependentOmegaGeometry

set_option maxRecDepth 3000
set_option maxHeartbeats 750000

/-- Exact CMP95-supported sites inside one generated CMP99 regional carrier. -/
noncomputable def generatedCMP95SectionCSourceHeadSupportSites
    (D : CMP99SourceDependentOmegaGeometry
      (FinBox 4 (2 * Q)) j ScaleSite Scaled
      (cmp99SourceTildePiLargeBlocks cell 3)
      (cmp99SourceTildePiLargeBlocks cell 4) dist gap)
    (hpi5 : D.fineRegion (cmp99OmegaZeroIndex j) ⊆
      cmp99SourceTildePiLargeBlocks cell 5)
    (s : Fin (j + 2)) :
    Finset (ActiveGaugeRegion.Site (D.operatorCoarseRegion hpi5 s)) := by
  classical
  exact Finset.univ.filter fun target =>
    cmp95SourcePeriodicCoarseCellSupport Q cell target.1

@[simp] theorem mem_generatedCMP95SectionCSourceHeadSupportSites_iff
    (D : CMP99SourceDependentOmegaGeometry
      (FinBox 4 (2 * Q)) j ScaleSite Scaled
      (cmp99SourceTildePiLargeBlocks cell 3)
      (cmp99SourceTildePiLargeBlocks cell 4) dist gap)
    (hpi5 : D.fineRegion (cmp99OmegaZeroIndex j) ⊆
      cmp99SourceTildePiLargeBlocks cell 5)
    (s : Fin (j + 2))
    (target : ActiveGaugeRegion.Site (D.operatorCoarseRegion hpi5 s)) :
    target ∈ D.generatedCMP95SectionCSourceHeadSupportSites hpi5 s ↔
      cmp95SourcePeriodicCoarseCellSupport Q cell target.1 := by
  classical
  rw [generatedCMP95SectionCSourceHeadSupportSites, Finset.mem_filter]
  exact and_iff_right (Finset.mem_univ target)

/-- At most 81 sites of any active regional carrier lie in the exact
periodized support of one CMP95 source cell. -/
theorem card_generatedCMP95SectionCSourceHeadSupportSites_le
    (D : CMP99SourceDependentOmegaGeometry
      (FinBox 4 (2 * Q)) j ScaleSite Scaled
      (cmp99SourceTildePiLargeBlocks cell 3)
      (cmp99SourceTildePiLargeBlocks cell 4) dist gap)
    (hpi5 : D.fineRegion (cmp99OmegaZeroIndex j) ⊆
      cmp99SourceTildePiLargeBlocks cell 5)
    (s : Fin (j + 2)) :
    (D.generatedCMP95SectionCSourceHeadSupportSites hpi5 s).card ≤ 81 := by
  classical
  let supported := D.generatedCMP95SectionCSourceHeadSupportSites hpi5 s
  let blocks := supported.image fun target => target.1
  have hinjective : Function.Injective
      (fun target : ActiveGaugeRegion.Site (D.operatorCoarseRegion hpi5 s) =>
        target.1) := by
    intro left right h
    exact Subtype.ext h
  have hcardImage : blocks.card = supported.card := by
    exact Finset.card_image_of_injective _ hinjective
  have hsubset : blocks ⊆ cmp95SourcePeriodicCoarseCellSupportFinset cell := by
    intro block hblock
    rw [Finset.mem_image] at hblock
    obtain ⟨target, htarget, rfl⟩ := hblock
    apply (mem_cmp95SourcePeriodicCoarseCellSupportFinset_iff cell target.1).mpr
    exact (D.mem_generatedCMP95SectionCSourceHeadSupportSites_iff
      hpi5 s target).mp htarget
  change supported.card ≤ 81
  rw [← hcardImage]
  exact (Finset.card_le_card hsubset).trans
    (card_filter_cmp95SourcePeriodicCoarseCellSupport_le cell)

/-- The exact support reduces the source-generated head weighted row from
the ambient `tilde Pi^5` budget `20736` to the volume-independent support
budget `81`. -/
theorem generatedCMP95SectionCSourceHeadFactorCoordinates_weightedRow_supportSharp
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
    FinitePiLpTypedWeightedRowKernelBound
      (D.generatedSectionCSourceHeadFactorCertificate
        (cmp95SourcePeriodicCoarseSquarePartition P Q) hpi5 s hM depth
          hspacing background budget fineSmall hsmall).operator
      (activeGaugeRegionSiteFinBoxDist (D.operatorCoarseRegion hpi5 s))
      (cmp99SourceGeneratedCMP95SectionCHeadWeightedRowAmplitude
        M depth spacing epsilon rate) rate := by
  classical
  let F := (D.generatedSectionCSourceHeadFactorCertificate
    (cmp95SourcePeriodicCoarseSquarePartition P Q) hpi5 s hM depth
      hspacing background budget fineSmall hsmall).operator
  let A := cmp99SourceGeneratedPhysicalCoarseCovarianceNormBound
    M depth spacing epsilon
  let supported := D.generatedCMP95SectionCSourceHeadSupportSites hpi5 s
  have hA : 0 ≤ A := by
    exact (norm_nonneg F).trans
      (D.norm_generatedSectionCSourceHeadFactorCoordinates_le
        (cmp95SourcePeriodicCoarseSquarePartition P Q) hpi5 s hM depth
          hspacing background budget fineSmall hsmall)
  have hnorm : ‖F‖ ≤ A :=
    D.norm_generatedSectionCSourceHeadFactorCoordinates_le
      (cmp95SourcePeriodicCoarseSquarePartition P Q) hpi5 s hM depth
        hspacing background budget fineSmall hsmall
  have hentry := finitePiLpTypedKernelBound_const_opNorm F
  have hdiam : ∀ left right,
      activeGaugeRegionSiteFinBoxDist (D.operatorCoarseRegion hpi5 s)
        left right ≤ 1 + 2 * 5 :=
    D.operatorCoarseRegion_siteFinBoxDist_le_pi5 hpi5 s
  have hcard : supported.card ≤ 81 := by
    exact D.card_generatedCMP95SectionCSourceHeadSupportSites_le hpi5 s
  refine ⟨mul_nonneg (mul_nonneg hA (Real.exp_pos _).le)
      (by norm_num), hrate.le, ?_⟩
  intro source v
  let f := fun target : ActiveGaugeRegion.Site
      (D.operatorCoarseRegion hpi5 s) =>
    Real.exp (rate *
      (activeGaugeRegionSiteFinBoxDist
        (D.operatorCoarseRegion hpi5 s) target source : ℝ)) *
      ‖F (singleFinitePiLp source v) target‖
  have hsumSupport : (∑ target, f target) = ∑ target ∈ supported, f target := by
    refine (Finset.sum_subset (Finset.subset_univ supported) ?_).symm
    intro target _ htarget
    have houtside :
        ¬ cmp95SourcePeriodicCoarseCellSupport Q cell target.1 := by
      simpa [supported,
        D.mem_generatedCMP95SectionCSourceHeadSupportSites_iff] using htarget
    have hzero : F (singleFinitePiLp source v) target = 0 := by
      simpa [F, generatedSectionCSourceHeadFactorCertificate] using
        D.generatedCMP95SectionCSourceHeadFactorCoordinates_apply_single_eq_zero_of_target
          P hpi5 s hM depth hspacing background budget fineSmall hsmall
            source target v houtside
    dsimp [f]
    rw [hzero, norm_zero, mul_zero]
  change (∑ target, f target) ≤ _
  rw [hsumSupport]
  calc
    ∑ target ∈ supported, f target ≤
        ∑ _target ∈ supported,
          (A * Real.exp (rate * ((1 + 2 * 5 : ℕ) : ℝ))) * ‖v‖ := by
      apply Finset.sum_le_sum
      intro target htarget
      have hdistNat := hdiam target source
      have hdist :
          (activeGaugeRegionSiteFinBoxDist
            (D.operatorCoarseRegion hpi5 s) target source : ℝ) ≤
              ((1 + 2 * 5 : ℕ) : ℝ) := by
        exact_mod_cast hdistNat
      have hexp :
          Real.exp (rate *
            (activeGaugeRegionSiteFinBoxDist
              (D.operatorCoarseRegion hpi5 s) target source : ℝ)) ≤
            Real.exp (rate * ((1 + 2 * 5 : ℕ) : ℝ)) := by
        apply Real.exp_le_exp.mpr
        exact mul_le_mul_of_nonneg_left hdist hrate.le
      calc
        f target ≤ Real.exp (rate *
              (activeGaugeRegionSiteFinBoxDist
                (D.operatorCoarseRegion hpi5 s) target source : ℝ)) *
            (A * ‖v‖) := by
          apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
          exact (hentry source target v).trans
            (mul_le_mul_of_nonneg_right hnorm (norm_nonneg v))
        _ ≤ Real.exp (rate * ((1 + 2 * 5 : ℕ) : ℝ)) *
            (A * ‖v‖) :=
          mul_le_mul_of_nonneg_right hexp
            (mul_nonneg hA (norm_nonneg v))
        _ = (A * Real.exp (rate * ((1 + 2 * 5 : ℕ) : ℝ))) * ‖v‖ := by
          ring
    _ = (supported.card : ℝ) *
        ((A * Real.exp (rate * ((1 + 2 * 5 : ℕ) : ℝ))) * ‖v‖) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (81 : ℝ) *
        ((A * Real.exp (rate * ((1 + 2 * 5 : ℕ) : ℝ))) * ‖v‖) := by
      gcongr
      exact_mod_cast hcard
    _ = cmp99SourceGeneratedCMP95SectionCHeadWeightedRowAmplitude
          M depth spacing epsilon rate * ‖v‖ := by
      simp only [cmp99SourceGeneratedCMP95SectionCHeadWeightedRowAmplitude, A]
      ring

end CMP99SourceDependentOmegaGeometry

end
end YangMills.RG
