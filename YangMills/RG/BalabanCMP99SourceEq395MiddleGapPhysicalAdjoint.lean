/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceEq395GlobalRegionalMiddleAmbientBridge
import YangMills.RG.BalabanCMP99SourceEq395ThirdBoundary

/-!
# The first CMP99 (3.95) atom as a physical rectangular adjoint

The global--regional middle gap in the grouped cell atom is not a new
operator.  After localization by the literal smooth cutoff it is exactly the
ambient lift of the adjoint of the rectangular source defect whose exponential
kernel bound has already been proved.  This file performs that final
source-to-ambient identification.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator RealInnerProductSpace

noncomputable section

universe v

variable {M Nc Q j : ℕ} [NeZero M] [NeZero Nc] [NeZero Q]
variable {ScaleSite : Fin (j + 2) → Type v}
variable [∀ r, DecidableEq (ScaleSite r)]
variable {Scaled : CMP99SourceScaledStratification
  (FinBox 4 (2 * Q)) (j + 2) ScaleSite}
variable {dist : FinBox 4 (2 * Q) → FinBox 4 (2 * Q) → ℕ}
variable {gap : Fin (j + 1) → ℕ}

namespace CMP99SourceDependentOmegaGeometry

set_option maxRecDepth 6000 in
set_option maxHeartbeats 12000000 in
/-- The global--regional middle difference, localized on the physical input,
is the ambient lift of the adjoint rectangular source defect localized on the
same input.  In particular no ambient-dimensional comparison is used. -/
theorem cmp99Eq395PhysicalMiddleGap_comp_smoothMultiplier_eq_liftedAdjoint
    (D : (cell : FinBox 4 Q) → CMP99SourceDependentOmegaGeometry
      (FinBox 4 (2 * Q)) j ScaleSite Scaled
      (cmp99SourceTildePiLargeBlocks cell 3)
      (cmp99SourceTildePiLargeBlocks cell 4) dist gap)
    (hpi5 : ∀ cell, (D cell).fineRegion (cmp99OmegaZeroIndex j) ⊆
      cmp99SourceTildePiLargeBlocks cell 5)
    (P : CMP95SourceSmoothPartitionProfile)
    (hM : 2 ≤ M) (depth : ℕ) {spacing epsilon : ℝ}
    (hspacing : 0 < spacing)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 M Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff 4 M (depth + 1)
      spacing epsilon < 1)
    (cell : FinBox 4 Q) :
    let OmegaSmall := (D cell).operatorCoarseRegion (hpi5 cell)
      (cmp99OmegaPi4Index j)
    let OmegaLarge := cmp99Eq395FullCoarseRegion (Q := Q)
    let C := (D cell).cmp99Eq395PhysicalGlobalRegionalMiddleDefectOnSource
      (hpi5 cell) hM depth hspacing background budget fineSmall hsmall
    let liftedAdjoint := (extendZeroZeroCLM (𝔤 := SUNLieCoord Nc) OmegaLarge).comp
      (C.adjoint.comp (restrictZeroCLM OmegaSmall))
    let A := cmp99Eq395PhysicalGlobalMiddle hM depth hspacing background
      budget fineSmall hsmall
    let AD := cmp99Eq395PhysicalMiddle D hpi5 hM depth hspacing background
      budget fineSmall hsmall cell
    let h := cmp99Eq395PhysicalSmoothMultiplier (Nc := Nc) P cell
    (A - AD).comp h = liftedAdjoint.comp h := by
  dsimp only
  let OmegaSmall := (D cell).operatorCoarseRegion (hpi5 cell)
    (cmp99OmegaPi4Index j)
  let OmegaLarge := cmp99Eq395FullCoarseRegion (Q := Q)
  let C := (D cell).cmp99Eq395PhysicalGlobalRegionalMiddleDefectOnSource
    (hpi5 cell) hM depth hspacing background budget fineSmall hsmall
  let liftedAdjoint := (extendZeroZeroCLM (𝔤 := SUNLieCoord Nc) OmegaLarge).comp
    (C.adjoint.comp (restrictZeroCLM OmegaSmall))
  let A := cmp99Eq395PhysicalGlobalMiddle hM depth hspacing background
    budget fineSmall hsmall
  let AD := cmp99Eq395PhysicalMiddle D hpi5 hM depth hspacing background
    budget fineSmall hsmall cell
  let proj := (extendZeroZeroCLM (𝔤 := SUNLieCoord Nc) OmegaSmall).comp
    (restrictZeroCLM OmegaSmall)
  let h := cmp99Eq395PhysicalSmoothMultiplier (Nc := Nc) P cell
  have hambient : liftedAdjoint = A.comp proj - AD := by
    simpa [liftedAdjoint, A, AD, proj, C, OmegaSmall, OmegaLarge,
      cmp99Eq395PhysicalMiddle] using
      ((D cell).cmp99Eq395PhysicalGlobalRegionalMiddleDefect_adjoint_ambient
        (hpi5 cell) hM depth hspacing background budget fineSmall hsmall)
  have hproj : proj.comp h = h := by
    simpa [proj, h, OmegaSmall] using
      ((D cell).cmp99Eq395PhysicalPi4Projector_comp_smoothMultiplier
        (hpi5 cell) (Nc := Nc) P)
  change (A - AD).comp h = liftedAdjoint.comp h
  rw [hambient]
  apply ContinuousLinearMap.ext
  intro f
  have hprojApply := congrArg (fun T : CMP99Eq395AmbientOperator Q Nc => T f) hproj
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply] at hprojApply ⊢
  rw [hprojApply]

/-- Source-faithful replacement of the first term in the grouped left defect:
the middle gap is now the already-controlled rectangular adjoint, while the
second summand remains the literal regional commutator. -/
theorem cmp99Eq395PhysicalGroupedLeftDefect_eq_liftedAdjoint_add_commutator
    (D : (cell : FinBox 4 Q) → CMP99SourceDependentOmegaGeometry
      (FinBox 4 (2 * Q)) j ScaleSite Scaled
      (cmp99SourceTildePiLargeBlocks cell 3)
      (cmp99SourceTildePiLargeBlocks cell 4) dist gap)
    (hpi5 : ∀ cell, (D cell).fineRegion (cmp99OmegaZeroIndex j) ⊆
      cmp99SourceTildePiLargeBlocks cell 5)
    (P : CMP95SourceSmoothPartitionProfile)
    (hM : 2 ≤ M) (depth : ℕ) {spacing epsilon : ℝ}
    (hspacing : 0 < spacing)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 M Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff 4 M (depth + 1)
      spacing epsilon < 1)
    (cell : FinBox 4 Q) :
    let OmegaSmall := (D cell).operatorCoarseRegion (hpi5 cell)
      (cmp99OmegaPi4Index j)
    let OmegaLarge := cmp99Eq395FullCoarseRegion (Q := Q)
    let C := (D cell).cmp99Eq395PhysicalGlobalRegionalMiddleDefectOnSource
      (hpi5 cell) hM depth hspacing background budget fineSmall hsmall
    let liftedAdjoint := (extendZeroZeroCLM (𝔤 := SUNLieCoord Nc) OmegaLarge).comp
      (C.adjoint.comp (restrictZeroCLM OmegaSmall))
    let AD := cmp99Eq395PhysicalMiddle D hpi5 hM depth hspacing background
      budget fineSmall hsmall cell
    let h := cmp99Eq395PhysicalSmoothMultiplier (Nc := Nc) P cell
    cmp99Eq395PhysicalGroupedLeftDefect D hpi5 P hM depth hspacing background
        budget fineSmall hsmall cell =
      liftedAdjoint * h + (AD * h - h * AD) := by
  dsimp only
  rw [cmp99Eq395PhysicalGroupedLeftDefect_eq_middleGap_add_commutator]
  let OmegaSmall := (D cell).operatorCoarseRegion (hpi5 cell)
    (cmp99OmegaPi4Index j)
  let OmegaLarge := cmp99Eq395FullCoarseRegion (Q := Q)
  let C := (D cell).cmp99Eq395PhysicalGlobalRegionalMiddleDefectOnSource
    (hpi5 cell) hM depth hspacing background budget fineSmall hsmall
  let liftedAdjoint := (extendZeroZeroCLM (𝔤 := SUNLieCoord Nc) OmegaLarge).comp
    (C.adjoint.comp (restrictZeroCLM OmegaSmall))
  let A := cmp99Eq395PhysicalGlobalMiddle hM depth hspacing background
    budget fineSmall hsmall
  let AD := cmp99Eq395PhysicalMiddle D hpi5 hM depth hspacing background
    budget fineSmall hsmall cell
  let h := cmp99Eq395PhysicalSmoothMultiplier (Nc := Nc) P cell
  have hgap : (A - AD).comp h = liftedAdjoint.comp h := by
    simpa [OmegaSmall, OmegaLarge, C, liftedAdjoint, A, AD, h] using
      (cmp99Eq395PhysicalMiddleGap_comp_smoothMultiplier_eq_liftedAdjoint
        D hpi5 P hM depth hspacing background budget fineSmall hsmall cell)
  change (A - AD).comp h + (AD.comp h - h.comp AD) =
    liftedAdjoint.comp h + (AD.comp h - h.comp AD)
  rw [hgap]

set_option maxRecDepth 6000 in
set_option maxHeartbeats 12000000 in
/-- Extending the adjoint rectangular source defect by zero preserves its
fixed-rate exponential kernel bound in the ambient physical block metric.
Sources outside `Pi^4` vanish exactly; the full target region contains every
ambient block. -/
theorem cmp99Eq395PhysicalGlobalRegionalMiddleDefect_liftedAdjoint_exponentialKernelBound
    (D : CMP99SourceDependentOmegaGeometry
      (FinBox 4 (2 * Q)) j ScaleSite Scaled
      (cmp99SourceTildePiLargeBlocks cell 3)
      (cmp99SourceTildePiLargeBlocks cell 4) dist gap)
    (hpi5 : D.fineRegion (cmp99OmegaZeroIndex j) ⊆
      cmp99SourceTildePiLargeBlocks cell 5)
    (hM : 2 ≤ M) (depth : ℕ) {spacing epsilon : ℝ}
    (hspacing : 0 < spacing)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 M Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff 4 M (depth + 1)
      spacing epsilon < 1) :
    let OmegaSmall := D.operatorCoarseRegion hpi5 (cmp99OmegaPi4Index j)
    let OmegaLarge := cmp99Eq395FullCoarseRegion (Q := Q)
    let C := D.cmp99Eq395PhysicalGlobalRegionalMiddleDefectOnSource hpi5 hM
      depth hspacing background budget fineSmall hsmall
    let liftedAdjoint := (extendZeroZeroCLM (𝔤 := SUNLieCoord Nc) OmegaLarge).comp
      (C.adjoint.comp (restrictZeroCLM OmegaSmall))
    FinitePiLpTypedExponentialKernelBound liftedAdjoint
      (fun target source => M ^ (depth + 1) * finBoxDist source target)
      (cmp99Eq395PhysicalGlobalRegionalMiddleDecayAmplitude
        M depth spacing epsilon)
      (cmp99SourceGeneratedCombesThomasRate
        4 M depth spacing epsilon / 12) := by
  dsimp only
  let OmegaSmall := D.operatorCoarseRegion hpi5 (cmp99OmegaPi4Index j)
  let OmegaLarge := cmp99Eq395FullCoarseRegion (Q := Q)
  let C := D.cmp99Eq395PhysicalGlobalRegionalMiddleDefectOnSource hpi5 hM
    depth hspacing background budget fineSmall hsmall
  have hC :=
    D.cmp99Eq395PhysicalGlobalRegionalMiddleDefectOnSource_adjoint_exponentialKernelBound
      hpi5 hM depth hspacing background budget fineSmall hsmall
  refine ⟨hC.1, hC.2.1, ?_⟩
  intro source target v
  by_cases hsource : source ∈ OmegaSmall.sites
  · let sourceOmega : ActiveGaugeRegion.Site OmegaSmall := ⟨source, hsource⟩
    let targetOmega : ActiveGaugeRegion.Site OmegaLarge :=
      ⟨target, by simp [OmegaLarge, cmp99Eq395FullCoarseRegion]⟩
    have hrestrict :
        restrictZeroCLM OmegaSmall (singleFinitePiLp source v) =
          singleFinitePiLp sourceOmega v := by
      apply PiLp.ext
      intro x
      by_cases hx : x.1 = source
      · have heq : x = sourceOmega := Subtype.ext hx
        subst x
        simp [restrictZeroCLM, sourceOmega]
      · have hne : x ≠ sourceOmega := by
          intro heq
          exact hx (congrArg Subtype.val heq)
        simp [restrictZeroCLM, singleFinitePiLp, hx, hne]
    have htarget : target ∈ OmegaLarge.sites := by
      simp [OmegaLarge, cmp99Eq395FullCoarseRegion]
    change ‖extendZeroZeroCLM OmegaLarge
        (C.adjoint (restrictZeroCLM OmegaSmall
          (singleFinitePiLp source v))) target‖ ≤ _
    rw [extendZeroZeroCLM_apply_of_mem OmegaLarge _ target htarget, hrestrict]
    change ‖C.adjoint (singleFinitePiLp sourceOmega v) targetOmega‖ ≤ _
    exact hC.2.2 sourceOmega targetOmega v
  · have hrestrict :
        restrictZeroCLM OmegaSmall (singleFinitePiLp source v) = 0 := by
      apply PiLp.ext
      intro x
      have hne : x.1 ≠ source := by
        intro heq
        apply hsource
        simpa [heq] using x.2
      simp [restrictZeroCLM, singleFinitePiLp, hne]
    change ‖extendZeroZeroCLM OmegaLarge
        (C.adjoint (restrictZeroCLM OmegaSmall
          (singleFinitePiLp source v))) target‖ ≤ _
    rw [hrestrict]
    simp only [map_zero, PiLp.zero_apply, norm_zero]
    exact mul_nonneg
      (mul_nonneg hC.1 (Real.exp_pos _).le) (norm_nonneg v)

/-- The first physical (3.95) middle-gap atom inherits the same fixed-rate,
volume-independent exponential kernel bound after multiplication by the
contractive smooth cutoff. -/
theorem cmp99Eq395PhysicalMiddleGap_comp_smoothMultiplier_exponentialKernelBound
    (D : (cell : FinBox 4 Q) → CMP99SourceDependentOmegaGeometry
      (FinBox 4 (2 * Q)) j ScaleSite Scaled
      (cmp99SourceTildePiLargeBlocks cell 3)
      (cmp99SourceTildePiLargeBlocks cell 4) dist gap)
    (hpi5 : ∀ cell, (D cell).fineRegion (cmp99OmegaZeroIndex j) ⊆
      cmp99SourceTildePiLargeBlocks cell 5)
    (P : CMP95SourceSmoothPartitionProfile)
    (hM : 2 ≤ M) (depth : ℕ) {spacing epsilon : ℝ}
    (hspacing : 0 < spacing)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 M Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff 4 M (depth + 1)
      spacing epsilon < 1)
    (cell : FinBox 4 Q) :
    let A := cmp99Eq395PhysicalGlobalMiddle hM depth hspacing background
      budget fineSmall hsmall
    let AD := cmp99Eq395PhysicalMiddle D hpi5 hM depth hspacing background
      budget fineSmall hsmall cell
    let h := cmp99Eq395PhysicalSmoothMultiplier (Nc := Nc) P cell
    FinitePiLpTypedExponentialKernelBound ((A - AD).comp h)
      (fun target source => M ^ (depth + 1) * finBoxDist source target)
      (cmp99Eq395PhysicalGlobalRegionalMiddleDecayAmplitude
        M depth spacing epsilon)
      (cmp99SourceGeneratedCombesThomasRate
        4 M depth spacing epsilon / 12) := by
  dsimp only
  let OmegaSmall := (D cell).operatorCoarseRegion (hpi5 cell)
    (cmp99OmegaPi4Index j)
  let OmegaLarge := cmp99Eq395FullCoarseRegion (Q := Q)
  let C := (D cell).cmp99Eq395PhysicalGlobalRegionalMiddleDefectOnSource
    (hpi5 cell) hM depth hspacing background budget fineSmall hsmall
  let liftedAdjoint := (extendZeroZeroCLM (𝔤 := SUNLieCoord Nc) OmegaLarge).comp
    (C.adjoint.comp (restrictZeroCLM OmegaSmall))
  let h := cmp99Eq395PhysicalSmoothMultiplier (Nc := Nc) P cell
  have hEq :
      (cmp99Eq395PhysicalGlobalMiddle hM depth hspacing background budget
          fineSmall hsmall -
        cmp99Eq395PhysicalMiddle D hpi5 hM depth hspacing background budget
          fineSmall hsmall cell).comp h = liftedAdjoint.comp h := by
    simpa [OmegaSmall, OmegaLarge, C, liftedAdjoint, h] using
      (cmp99Eq395PhysicalMiddleGap_comp_smoothMultiplier_eq_liftedAdjoint
        D hpi5 P hM depth hspacing background budget fineSmall hsmall cell)
  rw [hEq]
  apply finitePiLpTypedExponentialKernelBound_comp_scalarMultiplier_right
    (fun block : FinBox 4 (2 * Q) =>
      (cmp95SourcePeriodicCoarseSquarePartition P Q).value cell block)
  · intro block
    exact (cmp95SourcePeriodicCoarseSquarePartition P Q).norm_value_le_one
      cell block
  · simpa [liftedAdjoint, C, OmegaSmall, OmegaLarge] using
      (cmp99Eq395PhysicalGlobalRegionalMiddleDefect_liftedAdjoint_exponentialKernelBound
        (D cell) (hpi5 cell) hM depth hspacing background budget fineSmall hsmall)

end CMP99SourceDependentOmegaGeometry

end
