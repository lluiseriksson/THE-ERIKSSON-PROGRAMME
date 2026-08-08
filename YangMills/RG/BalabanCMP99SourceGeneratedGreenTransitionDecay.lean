/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceGeneratedCombesThomas
import YangMills.RG.BalabanCMP99SourceGeneratedLaplacianTransitionSupport
import YangMills.RG.BalabanCMP99SourceRegionalCombesThomas

/-!
# Exponential decay of generated consecutive Green mismatches

The generated mass cancels exactly from the rectangular precision defect.
This file first exposes the remaining nearest-neighbour defect as a typed
finite-range kernel, in preparation for composing it with the two generated
Combes--Thomas Green bounds.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator RealInnerProductSpace

noncomputable section

variable {d N Nc : ℕ} [NeZero d] [NeZero N] [NeZero Nc]

/-- Restriction of a surviving coordinate probe between arbitrary nested
active regions is the corresponding coordinate probe exactly. -/
theorem cmp99NestedActiveRegionRestriction_single_of_mem
    (OmegaSmall OmegaLarge : ActiveGaugeRegion d N)
    (hsub : OmegaSmall.sites ⊆ OmegaLarge.sites)
    (source : ActiveGaugeRegion.Site OmegaLarge)
    (hsource : source.1 ∈ OmegaSmall.sites) (v : SUNLieCoord Nc) :
    cmp99NestedActiveRegionRestriction OmegaSmall OmegaLarge
        (singleFinitePiLp source v) =
      singleFinitePiLp
        (⟨source.1, hsource⟩ : ActiveGaugeRegion.Site OmegaSmall) v := by
  apply PiLp.ext
  intro target
  have htargetLarge : target.1 ∈ OmegaLarge.sites := hsub target.2
  by_cases hval : target.1 = source.1
  · have hlargeEq :
        (⟨target.1, htargetLarge⟩ : ActiveGaugeRegion.Site OmegaLarge) =
          source := Subtype.ext hval
    have hsmallEq : target =
        (⟨source.1, hsource⟩ : ActiveGaugeRegion.Site OmegaSmall) :=
      Subtype.ext hval
    simp [cmp99NestedActiveRegionRestriction, restrictZeroCLM,
      extendZeroZeroCLM, htargetLarge, singleFinitePiLp, hlargeEq, hsmallEq]
  · have hlargeNe :
        (⟨target.1, htargetLarge⟩ : ActiveGaugeRegion.Site OmegaLarge) ≠
          source := fun h => hval (congrArg Subtype.val h)
    have hsmallNe : target ≠
        (⟨source.1, hsource⟩ : ActiveGaugeRegion.Site OmegaSmall) :=
      fun h => hval (congrArg Subtype.val h)
    simp [cmp99NestedActiveRegionRestriction, restrictZeroCLM,
      extendZeroZeroCLM, htargetLarge, singleFinitePiLp, hlargeNe, hsmallNe]

/-- A coordinate probe removed by nested restriction becomes zero. -/
theorem cmp99NestedActiveRegionRestriction_single_of_not_mem
    (OmegaSmall OmegaLarge : ActiveGaugeRegion d N)
    (source : ActiveGaugeRegion.Site OmegaLarge)
    (hsource : source.1 ∉ OmegaSmall.sites) (v : SUNLieCoord Nc) :
    cmp99NestedActiveRegionRestriction OmegaSmall OmegaLarge
        (singleFinitePiLp source v) = 0 := by
  apply PiLp.ext
  intro target
  by_cases htargetLarge : target.1 ∈ OmegaLarge.sites
  · have hne :
        (⟨target.1, htargetLarge⟩ : ActiveGaugeRegion.Site OmegaLarge) ≠
          source := by
      intro h
      apply hsource
      exact h ▸ target.2
    simp [cmp99NestedActiveRegionRestriction, restrictZeroCLM,
      extendZeroZeroCLM, htargetLarge, singleFinitePiLp, hne]
  · simp [cmp99NestedActiveRegionRestriction, restrictZeroCLM,
      extendZeroZeroCLM, htargetLarge]

/-- The rectangular defect of two nested arbitrary-region source
Laplacians has exact nearest-neighbour range. -/
theorem cmp99NestedLaplacianPrecisionDefect_finiteRange_one
    (OmegaSmall OmegaLarge : ActiveGaugeRegion d N)
    (hsub : OmegaSmall.sites ⊆ OmegaLarge.sites)
    (rho : SUNAdjointModel Nc) (U : PhysicalGaugeBackground d N Nc)
    (spacing : ℝ) :
    FinitePiLpTypedFiniteRange
      (ι := ActiveGaugeRegion.Site OmegaLarge)
      (κ := ActiveGaugeRegion.Site OmegaSmall) (g := SUNLieCoord Nc)
      (cmp99TypedPrecisionDefect
        (cmp99ActiveRegionSourceCovariantLaplacian OmegaLarge rho U spacing)
        (cmp99ActiveRegionSourceCovariantLaplacian OmegaSmall rho U spacing)
        (cmp99NestedActiveRegionRestriction OmegaSmall OmegaLarge))
      (fun target source => finBoxDist target.1 source.1) 1 := by
  intro source target v hfar
  change 1 < finBoxDist target.1 source.1 at hfar
  let targetLarge : ActiveGaugeRegion.Site OmegaLarge :=
    ⟨target.1, hsub target.2⟩
  have hlargeFar : 1 <
      (fun x y : ActiveGaugeRegion.Site OmegaLarge => finBoxDist x.1 y.1)
        targetLarge source := by
    exact hfar
  have hlarge := cmp99ActiveRegionSourceCovariantLaplacian_finiteRange_one
    OmegaLarge rho U spacing source targetLarge v hlargeFar
  have hrestrictLarge :
      cmp99NestedActiveRegionRestriction OmegaSmall OmegaLarge
        (cmp99ActiveRegionSourceCovariantLaplacian OmegaLarge rho U spacing
          (singleFinitePiLp source v)) target =
      cmp99ActiveRegionSourceCovariantLaplacian OmegaLarge rho U spacing
        (singleFinitePiLp source v) targetLarge := by
    simp [cmp99NestedActiveRegionRestriction, restrictZeroCLM,
      extendZeroZeroCLM, targetLarge, hsub target.2]
  by_cases hsource : source.1 ∈ OmegaSmall.sites
  · let sourceSmall : ActiveGaugeRegion.Site OmegaSmall :=
      ⟨source.1, hsource⟩
    have hsmallFar : 1 <
        (fun x y : ActiveGaugeRegion.Site OmegaSmall => finBoxDist x.1 y.1)
          target sourceSmall := hfar
    have hsmall := cmp99ActiveRegionSourceCovariantLaplacian_finiteRange_one
      OmegaSmall rho U spacing sourceSmall target v hsmallFar
    rw [cmp99TypedPrecisionDefect, ContinuousLinearMap.sub_apply,
      PiLp.sub_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
      hrestrictLarge,
      cmp99NestedActiveRegionRestriction_single_of_mem
        OmegaSmall OmegaLarge hsub source hsource v,
      hlarge, hsmall, sub_zero]
  · rw [cmp99TypedPrecisionDefect, ContinuousLinearMap.sub_apply,
      PiLp.sub_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
      hrestrictLarge,
      cmp99NestedActiveRegionRestriction_single_of_not_mem
        OmegaSmall OmegaLarge source hsource v,
      map_zero, hlarge]
    simp

set_option synthInstance.maxHeartbeats 100000 in
set_option maxHeartbeats 800000 in
/-- Uniform rectangular entry budget for the nested Laplacian defect.  Each
of its two nearest-neighbour pieces is bounded by the physical Laplacian
operator norm `4*d/spacing^2`. -/
theorem cmp99NestedLaplacianPrecisionDefect_kernelBound
    (OmegaSmall OmegaLarge : ActiveGaugeRegion d N)
    (hsub : OmegaSmall.sites ⊆ OmegaLarge.sites)
    (rho : SUNAdjointModel Nc) (U : PhysicalGaugeBackground d N Nc)
    {spacing : ℝ} (hspacing : 0 < spacing) :
    FinitePiLpTypedKernelBound
      (ι := ActiveGaugeRegion.Site OmegaLarge)
      (κ := ActiveGaugeRegion.Site OmegaSmall) (g := SUNLieCoord Nc)
      (cmp99TypedPrecisionDefect
        (cmp99ActiveRegionSourceCovariantLaplacian OmegaLarge rho U spacing)
        (cmp99ActiveRegionSourceCovariantLaplacian OmegaSmall rho U spacing)
        (cmp99NestedActiveRegionRestriction OmegaSmall OmegaLarge))
      (fun _ _ => 8 * d / spacing ^ 2) := by
  let beta : ℝ := 4 * d / spacing ^ 2
  have hlargeKernel : FinitePiLpKernelBound
      (ι := ActiveGaugeRegion.Site OmegaLarge) (g := SUNLieCoord Nc)
      (cmp99ActiveRegionSourceCovariantLaplacian OmegaLarge rho U spacing)
      (fun _ _ => beta) := by
    intro source target v
    calc
      ‖cmp99ActiveRegionSourceCovariantLaplacian OmegaLarge rho U spacing
          (singleFinitePiLp source v) target‖ ≤
        ‖cmp99ActiveRegionSourceCovariantLaplacian
          OmegaLarge rho U spacing‖ * ‖v‖ :=
        finitePiLpKernelBound_const_opNorm _ source target v
      _ ≤ beta * ‖v‖ := mul_le_mul_of_nonneg_right
        (by simpa [beta] using
          (norm_cmp99ActiveRegionSourceCovariantLaplacian_le
            OmegaLarge rho U hspacing)) (norm_nonneg v)
  have hsmallKernel : FinitePiLpKernelBound
      (ι := ActiveGaugeRegion.Site OmegaSmall) (g := SUNLieCoord Nc)
      (cmp99ActiveRegionSourceCovariantLaplacian OmegaSmall rho U spacing)
      (fun _ _ => beta) := by
    intro source target v
    calc
      ‖cmp99ActiveRegionSourceCovariantLaplacian OmegaSmall rho U spacing
          (singleFinitePiLp source v) target‖ ≤
        ‖cmp99ActiveRegionSourceCovariantLaplacian
          OmegaSmall rho U spacing‖ * ‖v‖ :=
        finitePiLpKernelBound_const_opNorm _ source target v
      _ ≤ beta * ‖v‖ := mul_le_mul_of_nonneg_right
        (by simpa [beta] using
          (norm_cmp99ActiveRegionSourceCovariantLaplacian_le
            OmegaSmall rho U hspacing)) (norm_nonneg v)
  intro source target v
  let targetLarge : ActiveGaugeRegion.Site OmegaLarge :=
    ⟨target.1, hsub target.2⟩
  have hrestrictLarge :
      cmp99NestedActiveRegionRestriction OmegaSmall OmegaLarge
        (cmp99ActiveRegionSourceCovariantLaplacian OmegaLarge rho U spacing
          (singleFinitePiLp source v)) target =
      cmp99ActiveRegionSourceCovariantLaplacian OmegaLarge rho U spacing
        (singleFinitePiLp source v) targetLarge := by
    simp [cmp99NestedActiveRegionRestriction, restrictZeroCLM,
      extendZeroZeroCLM, targetLarge, hsub target.2]
  have hleft :
      ‖cmp99NestedActiveRegionRestriction OmegaSmall OmegaLarge
        (cmp99ActiveRegionSourceCovariantLaplacian OmegaLarge rho U spacing
          (singleFinitePiLp source v)) target‖ ≤ beta * ‖v‖ := by
    rw [hrestrictLarge]
    exact hlargeKernel source targetLarge v
  have hright :
      ‖cmp99ActiveRegionSourceCovariantLaplacian OmegaSmall rho U spacing
        (cmp99NestedActiveRegionRestriction OmegaSmall OmegaLarge
          (singleFinitePiLp source v)) target‖ ≤ beta * ‖v‖ := by
    by_cases hsource : source.1 ∈ OmegaSmall.sites
    · rw [cmp99NestedActiveRegionRestriction_single_of_mem
        OmegaSmall OmegaLarge hsub source hsource v]
      exact hsmallKernel ⟨source.1, hsource⟩ target v
    · rw [cmp99NestedActiveRegionRestriction_single_of_not_mem
        OmegaSmall OmegaLarge source hsource v, map_zero]
      simp only [PiLp.zero_apply, norm_zero]
      have hbeta : 0 ≤ beta := by dsimp [beta]; positivity
      exact mul_nonneg hbeta (norm_nonneg v)
  rw [cmp99TypedPrecisionDefect, ContinuousLinearMap.sub_apply,
    PiLp.sub_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply]
  calc
    ‖cmp99NestedActiveRegionRestriction OmegaSmall OmegaLarge
          (cmp99ActiveRegionSourceCovariantLaplacian OmegaLarge rho U spacing
            (singleFinitePiLp source v)) target -
        cmp99ActiveRegionSourceCovariantLaplacian OmegaSmall rho U spacing
          (cmp99NestedActiveRegionRestriction OmegaSmall OmegaLarge
            (singleFinitePiLp source v)) target‖ ≤
      ‖cmp99NestedActiveRegionRestriction OmegaSmall OmegaLarge
          (cmp99ActiveRegionSourceCovariantLaplacian OmegaLarge rho U spacing
            (singleFinitePiLp source v)) target‖ +
        ‖cmp99ActiveRegionSourceCovariantLaplacian OmegaSmall rho U spacing
          (cmp99NestedActiveRegionRestriction OmegaSmall OmegaLarge
            (singleFinitePiLp source v)) target‖ := norm_sub_le _ _
    _ ≤ beta * ‖v‖ + beta * ‖v‖ := add_le_add hleft hright
    _ = (8 * d / spacing ^ 2) * ‖v‖ := by
      dsimp [beta]
      ring

set_option maxHeartbeats 800000 in
/-- Every four-dimensional active-region shell sum is bounded by the same
volume-independent polynomial-shell series used in the source analysis. -/
theorem activeGaugeRegion_finBoxDist_exp_sum_le
    {N : ℕ} [NeZero N] (Omega : ActiveGaugeRegion 4 N)
    (x : ActiveGaugeRegion.Site Omega)
    {sigma : ℝ} (hsigma : 0 < sigma) :
    ∑ y : ActiveGaugeRegion.Site Omega,
      Real.exp (-(sigma * (finBoxDist x.1 y.1 : ℝ))) ≤
      cmp99OmegaSiteExpSumBound sigma := by
  unfold cmp99OmegaSiteExpSumBound
  have hN : ∀ k,
      ((Finset.univ.filter
        (fun y : ActiveGaugeRegion.Site Omega =>
          finBoxDist x.1 y.1 = k)).card : ℝ) ≤
        (((2 * k + 1) ^ 4 : ℕ) : ℝ) := by
    intro k
    exact_mod_cast (Finset.card_le_card
      (show Finset.univ.filter
          (fun y : ActiveGaugeRegion.Site Omega => finBoxDist x.1 y.1 = k) ⊆
        Finset.univ.filter (fun y => finBoxDist x.1 y.1 ≤ k) by
        intro y hy
        rw [Finset.mem_filter] at hy ⊢
        exact ⟨hy.1, hy.2.le⟩)).trans
          (activeGaugeRegion_finBoxDist_ball_card_le Omega x k)
  have hsummable : Summable
      (fun k : ℕ => (((2 * k + 1) ^ 4 : ℕ) : ℝ) *
        Real.exp (-sigma * (k : ℝ))) := by
    simpa only [neg_mul] using summable_cmp99OmegaSiteExpSumBound hsigma
  simpa only [neg_mul] using
    (lattice_exp_sum_le_of_shell
      (fun y : ActiveGaugeRegion.Site Omega => finBoxDist x.1 y.1)
      (σ := sigma) (fun k => (((2 * k + 1) ^ 4 : ℕ) : ℝ))
      hN hsummable)

universe v

variable {Q M j : ℕ} [NeZero Q] [NeZero M]
variable {cell : FinBox 4 Q}
variable {ScaleSite : Fin (j + 2) → Type v}
variable [∀ r, DecidableEq (ScaleSite r)]
variable {Scaled : CMP99SourceScaledStratification
  (FinBox 4 (2 * Q)) (j + 2) ScaleSite}
variable {dist : FinBox 4 (2 * Q) → FinBox 4 (2 * Q) → ℕ}
variable {gap : Fin (j + 1) → ℕ}

namespace CMP99SourceDependentOmegaGeometry

/-- After exact generated-mass cancellation, the complete physical precision
defect has nearest-neighbour range. -/
theorem generatedPhysicalPrecisionDefect_finiteRange_one
    (D : CMP99SourceDependentOmegaGeometry
      (FinBox 4 (2 * Q)) j ScaleSite Scaled
      (cmp99SourceTildePiLargeBlocks cell 3)
      (cmp99SourceTildePiLargeBlocks cell 4) dist gap)
    (hpi5 : D.fineRegion (cmp99OmegaZeroIndex j) ⊆
      cmp99SourceTildePiLargeBlocks cell 5)
    (r : Fin (j + 1)) (hM : 2 ≤ M) (depth : ℕ)
    (spacing epsilon : ℝ)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 M Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon) :
    FinitePiLpTypedFiniteRange
      (ι := ActiveGaugeRegion.Site
        (D.operatorRegion (M := M) hpi5
          (cmp99OmegaTransitionIndex r) (depth + 1)))
      (κ := ActiveGaugeRegion.Site
        (D.operatorRegion (M := M) hpi5
          (cmp99OmegaTransitionNextIndex r) (depth + 1)))
      (g := SUNLieCoord Nc)
      (cmp99TypedPrecisionDefect
        (cmp99SourceGeneratedPhysicalPrecision (by norm_num) hM
          (D.operatorCoarseRegion hpi5 (cmp99OmegaTransitionIndex r))
          depth spacing epsilon background budget fineSmall)
        (cmp99SourceGeneratedPhysicalPrecision (by norm_num) hM
          (D.operatorCoarseRegion hpi5 (cmp99OmegaTransitionNextIndex r))
          depth spacing epsilon background budget fineSmall)
        (D.generatedTransitionRestriction (M := M) (Nc := Nc) hpi5 r
          (depth + 1)))
      (fun target source => finBoxDist target.1 source.1) 1 := by
  have hbase := cmp99NestedLaplacianPrecisionDefect_finiteRange_one
      (D.operatorRegion (M := M) hpi5
        (cmp99OmegaTransitionNextIndex r) (depth + 1))
      (D.operatorRegion (M := M) hpi5
        (cmp99OmegaTransitionIndex r) (depth + 1))
      (D.operatorRegion_transition_subset hpi5 r (depth + 1))
      (matrixSUNAdjointModel Nc) background spacing
  have hdef := D.generatedPhysicalPrecisionDefect_eq_laplacianDefect
    hpi5 r hM depth spacing epsilon background budget fineSmall
  have hbase' : FinitePiLpTypedFiniteRange
      (cmp99TypedPrecisionDefect
        (cmp99ActiveRegionSourceCovariantLaplacian
          (D.operatorRegion (M := M) hpi5
            (cmp99OmegaTransitionIndex r) (depth + 1))
          (matrixSUNAdjointModel Nc) background spacing)
        (cmp99ActiveRegionSourceCovariantLaplacian
          (D.operatorRegion (M := M) hpi5
            (cmp99OmegaTransitionNextIndex r) (depth + 1))
          (matrixSUNAdjointModel Nc) background spacing)
        (D.generatedTransitionRestriction (M := M) (Nc := Nc) hpi5 r
          (depth + 1)))
      (fun target source => finBoxDist target.1 source.1) 1 := by
    simpa [generatedTransitionRestriction,
      cmp99NestedActiveRegionRestriction, operatorRegion] using hbase
  rw [← hdef] at hbase'
  exact hbase'

/-- The complete generated precision defect has the explicit rectangular
entry budget `32/spacing^2`; the generated mass contributes exactly zero. -/
theorem generatedPhysicalPrecisionDefect_kernelBound
    (D : CMP99SourceDependentOmegaGeometry
      (FinBox 4 (2 * Q)) j ScaleSite Scaled
      (cmp99SourceTildePiLargeBlocks cell 3)
      (cmp99SourceTildePiLargeBlocks cell 4) dist gap)
    (hpi5 : D.fineRegion (cmp99OmegaZeroIndex j) ⊆
      cmp99SourceTildePiLargeBlocks cell 5)
    (r : Fin (j + 1)) (hM : 2 ≤ M) (depth : ℕ)
    {spacing epsilon : ℝ} (hspacing : 0 < spacing)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 M Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon) :
    FinitePiLpTypedKernelBound
      (ι := ActiveGaugeRegion.Site
        (D.operatorRegion (M := M) hpi5
          (cmp99OmegaTransitionIndex r) (depth + 1)))
      (κ := ActiveGaugeRegion.Site
        (D.operatorRegion (M := M) hpi5
          (cmp99OmegaTransitionNextIndex r) (depth + 1)))
      (g := SUNLieCoord Nc)
      (cmp99TypedPrecisionDefect
        (cmp99SourceGeneratedPhysicalPrecision (by norm_num) hM
          (D.operatorCoarseRegion hpi5 (cmp99OmegaTransitionIndex r))
          depth spacing epsilon background budget fineSmall)
        (cmp99SourceGeneratedPhysicalPrecision (by norm_num) hM
          (D.operatorCoarseRegion hpi5 (cmp99OmegaTransitionNextIndex r))
          depth spacing epsilon background budget fineSmall)
        (D.generatedTransitionRestriction (M := M) (Nc := Nc) hpi5 r
          (depth + 1)))
      (fun _ _ => 8 * (4 : ℝ) / spacing ^ 2) := by
  have hbase := cmp99NestedLaplacianPrecisionDefect_kernelBound
    (D.operatorRegion (M := M) hpi5
      (cmp99OmegaTransitionNextIndex r) (depth + 1))
    (D.operatorRegion (M := M) hpi5
      (cmp99OmegaTransitionIndex r) (depth + 1))
    (D.operatorRegion_transition_subset hpi5 r (depth + 1))
    (matrixSUNAdjointModel Nc) background hspacing
  have hdef := D.generatedPhysicalPrecisionDefect_eq_laplacianDefect
    hpi5 r hM depth spacing epsilon background budget fineSmall
  have hbase' : FinitePiLpTypedKernelBound
      (cmp99TypedPrecisionDefect
        (cmp99ActiveRegionSourceCovariantLaplacian
          (D.operatorRegion (M := M) hpi5
            (cmp99OmegaTransitionIndex r) (depth + 1))
          (matrixSUNAdjointModel Nc) background spacing)
        (cmp99ActiveRegionSourceCovariantLaplacian
          (D.operatorRegion (M := M) hpi5
            (cmp99OmegaTransitionNextIndex r) (depth + 1))
          (matrixSUNAdjointModel Nc) background spacing)
        (D.generatedTransitionRestriction (M := M) (Nc := Nc) hpi5 r
          (depth + 1)))
      (fun _ _ => 8 * (4 : ℝ) / spacing ^ 2) := by
    simpa [generatedTransitionRestriction,
      cmp99NestedActiveRegionRestriction, operatorRegion] using hbase
  rw [← hdef] at hbase'
  exact hbase'

set_option maxHeartbeats 1200000 in
/-- The exact range-one generated defect is exponentially localized at the
same canonical rate as the two generated Greens. -/
theorem generatedPhysicalPrecisionDefect_exponentialKernelBound
    (D : CMP99SourceDependentOmegaGeometry
      (FinBox 4 (2 * Q)) j ScaleSite Scaled
      (cmp99SourceTildePiLargeBlocks cell 3)
      (cmp99SourceTildePiLargeBlocks cell 4) dist gap)
    (hpi5 : D.fineRegion (cmp99OmegaZeroIndex j) ⊆
      cmp99SourceTildePiLargeBlocks cell 5)
    (r : Fin (j + 1)) (hM : 2 ≤ M) (depth : ℕ)
    {spacing epsilon : ℝ} (hspacing : 0 < spacing)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 M Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff 4 M (depth + 1)
      spacing epsilon < 1) :
    let theta := cmp99SourceGeneratedCombesThomasRate
      4 M depth spacing epsilon
    let Ddef := cmp99TypedPrecisionDefect
      (cmp99SourceGeneratedPhysicalPrecision (by norm_num) hM
        (D.operatorCoarseRegion hpi5 (cmp99OmegaTransitionIndex r))
        depth spacing epsilon background budget fineSmall)
      (cmp99SourceGeneratedPhysicalPrecision (by norm_num) hM
        (D.operatorCoarseRegion hpi5 (cmp99OmegaTransitionNextIndex r))
        depth spacing epsilon background budget fineSmall)
      (D.generatedTransitionRestriction (M := M) (Nc := Nc) hpi5 r
        (depth + 1))
    FinitePiLpTypedExponentialKernelBound Ddef
      (fun target source => finBoxDist target.1 source.1)
      ((8 * (4 : ℝ) / spacing ^ 2) * Real.exp theta) theta := by
  let theta := cmp99SourceGeneratedCombesThomasRate
    4 M depth spacing epsilon
  let Ddef := cmp99TypedPrecisionDefect
    (cmp99SourceGeneratedPhysicalPrecision (by norm_num) hM
      (D.operatorCoarseRegion hpi5 (cmp99OmegaTransitionIndex r))
      depth spacing epsilon background budget fineSmall)
    (cmp99SourceGeneratedPhysicalPrecision (by norm_num) hM
      (D.operatorCoarseRegion hpi5 (cmp99OmegaTransitionNextIndex r))
      depth spacing epsilon background budget fineSmall)
    (D.generatedTransitionRestriction (M := M) (Nc := Nc) hpi5 r
      (depth + 1))
  have htheta : 0 < theta :=
    cmp99SourceGeneratedCombesThomasRate_pos 4 M depth hspacing hsmall
  have hrange : FinitePiLpTypedFiniteRange Ddef
      (fun target source => finBoxDist target.1 source.1) 1 := by
    exact D.generatedPhysicalPrecisionDefect_finiteRange_one
      hpi5 r hM depth spacing epsilon background budget fineSmall
  have hbound : FinitePiLpTypedKernelBound Ddef
      (fun _ _ => 8 * (4 : ℝ) / spacing ^ 2) := by
    exact D.generatedPhysicalPrecisionDefect_kernelBound
      hpi5 r hM depth hspacing background budget fineSmall
  simpa [theta, Ddef] using
    (finitePiLpTypedExponentialKernelBound_of_finiteRange
      (dist := fun target source => finBoxDist target.1 source.1)
      (beta := 8 * (4 : ℝ) / spacing ^ 2) (rate := theta) (R := 1)
      (by positivity) htheta Ddef hrange hbound)

/-- Explicit volume-independent amplitude of the full generated consecutive
Green mismatch. -/
noncomputable def cmp99SourceGeneratedPhysicalGreenTransitionDecayAmplitude
    (M depth : ℕ) (spacing epsilon : ℝ) : ℝ :=
  let c := cmp99SourceGeneratedCoercivity 4 M (depth + 1) spacing epsilon
  let theta := cmp99SourceGeneratedCombesThomasRate 4 M depth spacing epsilon
  let AG := 2 / c
  let AD := (8 * (4 : ℝ) / spacing ^ 2) * Real.exp theta
  let S := cmp99OmegaSiteExpSumBound (theta / 3)
  AG * (AD * AG * S) * S

set_option maxHeartbeats 4000000 in
/-- Generated C5 decay of the literal rectangular mismatch
`G_small R - R G_large`.  All constants are produced from the source
Poincare chain and the nearest-neighbour defect; no ambient-volume parameter
occurs. -/
theorem generatedPhysicalGreenTransition_exponentialKernelBound
    (D : CMP99SourceDependentOmegaGeometry
      (FinBox 4 (2 * Q)) j ScaleSite Scaled
      (cmp99SourceTildePiLargeBlocks cell 3)
      (cmp99SourceTildePiLargeBlocks cell 4) dist gap)
    (hpi5 : D.fineRegion (cmp99OmegaZeroIndex j) ⊆
      cmp99SourceTildePiLargeBlocks cell 5)
    (r : Fin (j + 1)) (hM : 2 ≤ M) (depth : ℕ)
    {spacing epsilon : ℝ} (hspacing : 0 < spacing)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 M Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff 4 M (depth + 1)
      spacing epsilon < 1) :
    FinitePiLpTypedExponentialKernelBound
      (D.generatedPhysicalGreenTransition (M := M) hpi5 r hM depth hspacing
        background budget fineSmall hsmall)
      (fun target source => finBoxDist target.1 source.1)
      (cmp99SourceGeneratedPhysicalGreenTransitionDecayAmplitude
        M depth spacing epsilon)
      (cmp99SourceGeneratedCombesThomasRate 4 M depth spacing epsilon / 3) := by
  let theta := cmp99SourceGeneratedCombesThomasRate 4 M depth spacing epsilon
  let c := cmp99SourceGeneratedCoercivity 4 M (depth + 1) spacing epsilon
  let AG := 2 / c
  let AD := (8 * (4 : ℝ) / spacing ^ 2) * Real.exp theta
  let S := cmp99OmegaSiteExpSumBound (theta / 3)
  let OmegaLarge := D.operatorRegion (M := M) hpi5
    (cmp99OmegaTransitionIndex r) (depth + 1)
  let OmegaSmall := D.operatorRegion (M := M) hpi5
    (cmp99OmegaTransitionNextIndex r) (depth + 1)
  let Glarge := cmp99SourceGeneratedPhysicalGreen (by norm_num) hM
    (D.operatorCoarseRegion hpi5 (cmp99OmegaTransitionIndex r)) depth
    hspacing background budget fineSmall hsmall
  let Gsmall := cmp99SourceGeneratedPhysicalGreen (by norm_num) hM
    (D.operatorCoarseRegion hpi5 (cmp99OmegaTransitionNextIndex r)) depth
    hspacing background budget fineSmall hsmall
  let Ddef := cmp99TypedPrecisionDefect
    (cmp99SourceGeneratedPhysicalPrecision (by norm_num) hM
      (D.operatorCoarseRegion hpi5 (cmp99OmegaTransitionIndex r))
      depth spacing epsilon background budget fineSmall)
    (cmp99SourceGeneratedPhysicalPrecision (by norm_num) hM
      (D.operatorCoarseRegion hpi5 (cmp99OmegaTransitionNextIndex r))
      depth spacing epsilon background budget fineSmall)
    (D.generatedTransitionRestriction (M := M) (Nc := Nc) hpi5 r
      (depth + 1))
  have htheta : 0 < theta :=
    cmp99SourceGeneratedCombesThomasRate_pos 4 M depth hspacing hsmall
  have hsigma : 0 < theta / 3 := by positivity
  have hS : 0 ≤ S := by
    dsimp [S, cmp99OmegaSiteExpSumBound]
    exact tsum_nonneg fun _ => mul_nonneg (Nat.cast_nonneg _)
      (Real.exp_pos _).le
  have hGlarge : FinitePiLpTypedExponentialKernelBound
      Glarge (fun x y : ActiveGaugeRegion.Site OmegaLarge =>
        finBoxDist x.1 y.1) AG theta := by
    exact finitePiLpTypedExponentialKernelBound_of_square
      (cmp99SourceGeneratedPhysicalGreen_canonicalExponentialKernelBound
        (by norm_num) hM
        (D.operatorCoarseRegion hpi5 (cmp99OmegaTransitionIndex r)) depth
        hspacing background budget fineSmall hsmall)
  have hGsmallTheta : FinitePiLpTypedExponentialKernelBound
      Gsmall (fun x y : ActiveGaugeRegion.Site OmegaSmall =>
        finBoxDist x.1 y.1) AG theta := by
    exact finitePiLpTypedExponentialKernelBound_of_square
      (cmp99SourceGeneratedPhysicalGreen_canonicalExponentialKernelBound
        (by norm_num) hM
        (D.operatorCoarseRegion hpi5 (cmp99OmegaTransitionNextIndex r)) depth
        hspacing background budget fineSmall hsmall)
  have hD : FinitePiLpTypedExponentialKernelBound Ddef
      (fun target : ActiveGaugeRegion.Site OmegaSmall =>
        fun source : ActiveGaugeRegion.Site OmegaLarge =>
          finBoxDist target.1 source.1) AD theta := by
    exact D.generatedPhysicalPrecisionDefect_exponentialKernelBound
      hpi5 r hM depth hspacing background budget fineSmall hsmall
  have hsumLarge : ∀ target : ActiveGaugeRegion.Site OmegaSmall,
      ∑ middle : ActiveGaugeRegion.Site OmegaLarge,
        Real.exp (-((theta / 3) * (finBoxDist target.1 middle.1 : ℝ))) ≤ S := by
    intro target
    let targetLarge : ActiveGaugeRegion.Site OmegaLarge :=
      ⟨target.1, D.operatorRegion_transition_subset hpi5 r (depth + 1) target.2⟩
    simpa [S, targetLarge] using
      activeGaugeRegion_finBoxDist_exp_sum_le OmegaLarge targetLarge hsigma
  have hDG : FinitePiLpTypedExponentialKernelBound
      (Ddef.comp Glarge)
      (fun target : ActiveGaugeRegion.Site OmegaSmall =>
        fun source : ActiveGaugeRegion.Site OmegaLarge =>
          finBoxDist target.1 source.1)
      (AD * AG * S) (theta - theta / 3) := by
    apply finitePiLpTypedExponentialKernelBound_comp
      (fun target : ActiveGaugeRegion.Site OmegaSmall =>
        fun middle : ActiveGaugeRegion.Site OmegaLarge =>
          finBoxDist target.1 middle.1)
      (fun middle source : ActiveGaugeRegion.Site OmegaLarge =>
        finBoxDist middle.1 source.1)
      (fun target : ActiveGaugeRegion.Site OmegaSmall =>
        fun source : ActiveGaugeRegion.Site OmegaLarge =>
          finBoxDist target.1 source.1)
      (fun target middle source => finBoxDist_triangle
        target.1 middle.1 source.1)
      hsigma (by linarith) hS hsumLarge Ddef Glarge hD hGlarge
  have hGsmall : FinitePiLpTypedExponentialKernelBound
      Gsmall (fun x y : ActiveGaugeRegion.Site OmegaSmall =>
        finBoxDist x.1 y.1) AG (theta - theta / 3) := by
    apply finitePiLpTypedExponentialKernelBound_mono_rate
      (by linarith) (by linarith) hGsmallTheta
  have hsumSmall : ∀ target : ActiveGaugeRegion.Site OmegaSmall,
      ∑ middle : ActiveGaugeRegion.Site OmegaSmall,
        Real.exp (-((theta / 3) * (finBoxDist target.1 middle.1 : ℝ))) ≤ S := by
    intro target
    exact activeGaugeRegion_finBoxDist_exp_sum_le OmegaSmall target hsigma
  have hcomp : FinitePiLpTypedExponentialKernelBound
      (Gsmall.comp (Ddef.comp Glarge))
      (fun target : ActiveGaugeRegion.Site OmegaSmall =>
        fun source : ActiveGaugeRegion.Site OmegaLarge =>
          finBoxDist target.1 source.1)
      (AG * (AD * AG * S) * S)
      ((theta - theta / 3) - theta / 3) := by
    apply finitePiLpTypedExponentialKernelBound_comp
      (fun target middle : ActiveGaugeRegion.Site OmegaSmall =>
        finBoxDist target.1 middle.1)
      (fun middle : ActiveGaugeRegion.Site OmegaSmall =>
        fun source : ActiveGaugeRegion.Site OmegaLarge =>
          finBoxDist middle.1 source.1)
      (fun target : ActiveGaugeRegion.Site OmegaSmall =>
        fun source : ActiveGaugeRegion.Site OmegaLarge =>
          finBoxDist target.1 source.1)
      (fun target middle source => finBoxDist_triangle
        target.1 middle.1 source.1)
      hsigma (by linarith) hS hsumSmall Gsmall (Ddef.comp Glarge)
      hGsmall hDG
  have hrateEq : (theta - theta / 3) - theta / 3 = theta / 3 := by ring
  rw [hrateEq] at hcomp
  rw [D.generatedPhysicalGreen_transition_resolvent hpi5 r hM depth hspacing
    background budget fineSmall hsmall]
  simpa [cmp99SourceGeneratedPhysicalGreenTransitionDecayAmplitude,
    theta, c, AG, AD, S, OmegaLarge, OmegaSmall, Glarge, Gsmall, Ddef]
    using hcomp

end CMP99SourceDependentOmegaGeometry

end

end YangMills.RG
