/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceGeneratedArbitraryCoarseMiddleTransition
import YangMills.RG.BalabanCMP99SourceGeneratedGreenTransitionDecay

/-!
# Decay of arbitrary nested generated Green transitions

This file runs the existing Combes--Thomas composition argument for any two
nested source regions.  It is the analytic form needed for the literal
`Pi^4 subset univ` comparison in CMP99 equation (3.95).
-/

namespace YangMills.RG

open YangMills Matrix
open CMP99SourceDependentOmegaGeometry
open scoped Matrix.Norms.L2Operator RealInnerProductSpace

noncomputable section

variable {Q M Nc : ℕ} [NeZero Q] [NeZero M] [NeZero Nc]

set_option maxHeartbeats 4000000 in
/-- Volume-independent exponential decay of the rectangular Green mismatch
for arbitrary nested source regions. -/
theorem cmp99SourceGeneratedNestedPhysicalGreenTransition_exponentialKernelBound
    (OmegaSmall OmegaLarge : ActiveGaugeRegion 4 (2 * Q))
    (hsub : OmegaSmall.sites ⊆ OmegaLarge.sites)
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
    FinitePiLpTypedExponentialKernelBound
      (cmp99SourceGeneratedNestedPhysicalGreenTransition OmegaSmall OmegaLarge
        hM depth hspacing background budget fineSmall hsmall)
      (fun target source => finBoxDist target.1 source.1)
      (cmp99SourceGeneratedPhysicalGreenTransitionDecayAmplitude
        M depth spacing epsilon)
      (cmp99SourceGeneratedCombesThomasRate 4 M depth spacing epsilon / 3) := by
  let theta := cmp99SourceGeneratedCombesThomasRate 4 M depth spacing epsilon
  let c := cmp99SourceGeneratedCoercivity 4 M (depth + 1) spacing epsilon
  let AG := 2 / c
  let AD := (8 * (4 : ℝ) / spacing ^ 2) * Real.exp theta
  let S := cmp99OmegaSiteExpSumBound (theta / 3)
  let FineSmall := cmp99IteratedLiftActiveRegion (M := M) OmegaSmall
    (depth + 1)
  let FineLarge := cmp99IteratedLiftActiveRegion (M := M) OmegaLarge
    (depth + 1)
  let R := cmp99NestedActiveRegionRestriction (g := SUNLieCoord Nc)
    FineSmall FineLarge
  let Glarge := cmp99SourceGeneratedPhysicalGreen (show 2 ≤ 4 by norm_num) hM
    OmegaLarge depth hspacing background budget fineSmall hsmall
  let Gsmall := cmp99SourceGeneratedPhysicalGreen (show 2 ≤ 4 by norm_num) hM
    OmegaSmall depth hspacing background budget fineSmall hsmall
  let Ddef := cmp99TypedPrecisionDefect
    (cmp99SourceGeneratedPhysicalPrecision (show 2 ≤ 4 by norm_num) hM
      OmegaLarge depth spacing epsilon background budget fineSmall)
    (cmp99SourceGeneratedPhysicalPrecision (show 2 ≤ 4 by norm_num) hM
      OmegaSmall depth spacing epsilon background budget fineSmall) R
  have hFineSub : FineSmall.sites ⊆ FineLarge.sites := by
    exact cmp99IteratedLiftActiveRegion_sites_mono hsub (depth + 1)
  have htheta : 0 < theta :=
    cmp99SourceGeneratedCombesThomasRate_pos 4 M depth hspacing hsmall
  have hsigma : 0 < theta / 3 := by positivity
  have hS : 0 ≤ S := by
    dsimp [S, cmp99OmegaSiteExpSumBound]
    exact tsum_nonneg fun _ => mul_nonneg (Nat.cast_nonneg _)
      (Real.exp_pos _).le
  have hGlarge : FinitePiLpTypedExponentialKernelBound
      Glarge (fun x y : ActiveGaugeRegion.Site FineLarge =>
        finBoxDist x.1 y.1) AG theta := by
    exact finitePiLpTypedExponentialKernelBound_of_square
      (cmp99SourceGeneratedPhysicalGreen_canonicalExponentialKernelBound
        (show 2 ≤ 4 by norm_num) hM OmegaLarge depth hspacing background
        budget fineSmall hsmall)
  have hGsmallTheta : FinitePiLpTypedExponentialKernelBound
      Gsmall (fun x y : ActiveGaugeRegion.Site FineSmall =>
        finBoxDist x.1 y.1) AG theta := by
    exact finitePiLpTypedExponentialKernelBound_of_square
      (cmp99SourceGeneratedPhysicalGreen_canonicalExponentialKernelBound
        (show 2 ≤ 4 by norm_num) hM OmegaSmall depth hspacing background
        budget fineSmall hsmall)
  have hD : FinitePiLpTypedExponentialKernelBound Ddef
      (fun target : ActiveGaugeRegion.Site FineSmall =>
        fun source : ActiveGaugeRegion.Site FineLarge =>
          finBoxDist target.1 source.1) AD theta := by
    have hrange : FinitePiLpTypedFiniteRange Ddef
        (fun target : ActiveGaugeRegion.Site FineSmall =>
          fun source : ActiveGaugeRegion.Site FineLarge =>
            finBoxDist target.1 source.1) 1 := by
      have hdef : Ddef = cmp99TypedPrecisionDefect
          (cmp99ActiveRegionSourceCovariantLaplacian FineLarge
            (matrixSUNAdjointModel Nc) background spacing)
          (cmp99ActiveRegionSourceCovariantLaplacian FineSmall
            (matrixSUNAdjointModel Nc) background spacing) R := by
        simpa [Ddef, R, FineSmall, FineLarge] using
          (cmp99SourceGeneratedNestedPhysicalPrecisionDefect_eq_laplacianDefect
            OmegaSmall OmegaLarge hsub hM depth spacing epsilon background budget
            fineSmall)
      rw [hdef]
      exact cmp99NestedLaplacianPrecisionDefect_finiteRange_one
        FineSmall FineLarge hFineSub (matrixSUNAdjointModel Nc) background spacing
    have hbound : FinitePiLpTypedKernelBound Ddef
        (fun _ _ => 8 * (4 : ℝ) / spacing ^ 2) := by
      have hdef : Ddef = cmp99TypedPrecisionDefect
          (cmp99ActiveRegionSourceCovariantLaplacian FineLarge
            (matrixSUNAdjointModel Nc) background spacing)
          (cmp99ActiveRegionSourceCovariantLaplacian FineSmall
            (matrixSUNAdjointModel Nc) background spacing) R := by
        simpa [Ddef, R, FineSmall, FineLarge] using
          (cmp99SourceGeneratedNestedPhysicalPrecisionDefect_eq_laplacianDefect
            OmegaSmall OmegaLarge hsub hM depth spacing epsilon background budget
            fineSmall)
      rw [hdef]
      exact cmp99NestedLaplacianPrecisionDefect_kernelBound
        FineSmall FineLarge hFineSub (matrixSUNAdjointModel Nc) background
        hspacing
    simpa [AD] using
      (finitePiLpTypedExponentialKernelBound_of_finiteRange
        (dist := fun target : ActiveGaugeRegion.Site FineSmall =>
          fun source : ActiveGaugeRegion.Site FineLarge =>
            finBoxDist target.1 source.1)
        (beta := 8 * (4 : ℝ) / spacing ^ 2) (rate := theta) (R := 1)
        (by positivity) htheta Ddef hrange hbound)
  have hsumLarge : ∀ target : ActiveGaugeRegion.Site FineSmall,
      ∑ middle : ActiveGaugeRegion.Site FineLarge,
        Real.exp (-((theta / 3) * (finBoxDist target.1 middle.1 : ℝ))) ≤ S := by
    intro target
    let targetLarge : ActiveGaugeRegion.Site FineLarge :=
      ⟨target.1, hFineSub target.2⟩
    simpa [S, targetLarge] using
      activeGaugeRegion_finBoxDist_exp_sum_le FineLarge targetLarge hsigma
  have hDG : FinitePiLpTypedExponentialKernelBound
      (Ddef.comp Glarge)
      (fun target : ActiveGaugeRegion.Site FineSmall =>
        fun source : ActiveGaugeRegion.Site FineLarge =>
          finBoxDist target.1 source.1)
      (AD * AG * S) (theta - theta / 3) := by
    apply finitePiLpTypedExponentialKernelBound_comp
      (fun target : ActiveGaugeRegion.Site FineSmall =>
        fun middle : ActiveGaugeRegion.Site FineLarge =>
          finBoxDist target.1 middle.1)
      (fun middle source : ActiveGaugeRegion.Site FineLarge =>
        finBoxDist middle.1 source.1)
      (fun target : ActiveGaugeRegion.Site FineSmall =>
        fun source : ActiveGaugeRegion.Site FineLarge =>
          finBoxDist target.1 source.1)
      (fun target middle source => finBoxDist_triangle
        target.1 middle.1 source.1)
      hsigma (by linarith) hS hsumLarge Ddef Glarge hD hGlarge
  have hGsmall : FinitePiLpTypedExponentialKernelBound
      Gsmall (fun x y : ActiveGaugeRegion.Site FineSmall =>
        finBoxDist x.1 y.1) AG (theta - theta / 3) := by
    apply finitePiLpTypedExponentialKernelBound_mono_rate
      (by linarith) (by linarith) hGsmallTheta
  have hsumSmall : ∀ target : ActiveGaugeRegion.Site FineSmall,
      ∑ middle : ActiveGaugeRegion.Site FineSmall,
        Real.exp (-((theta / 3) * (finBoxDist target.1 middle.1 : ℝ))) ≤ S := by
    intro target
    exact activeGaugeRegion_finBoxDist_exp_sum_le FineSmall target hsigma
  have hcomp : FinitePiLpTypedExponentialKernelBound
      (Gsmall.comp (Ddef.comp Glarge))
      (fun target : ActiveGaugeRegion.Site FineSmall =>
        fun source : ActiveGaugeRegion.Site FineLarge =>
          finBoxDist target.1 source.1)
      (AG * (AD * AG * S) * S)
      ((theta - theta / 3) - theta / 3) := by
    apply finitePiLpTypedExponentialKernelBound_comp
      (fun target middle : ActiveGaugeRegion.Site FineSmall =>
        finBoxDist target.1 middle.1)
      (fun middle : ActiveGaugeRegion.Site FineSmall =>
        fun source : ActiveGaugeRegion.Site FineLarge =>
          finBoxDist middle.1 source.1)
      (fun target : ActiveGaugeRegion.Site FineSmall =>
        fun source : ActiveGaugeRegion.Site FineLarge =>
          finBoxDist target.1 source.1)
      (fun target middle source => finBoxDist_triangle
        target.1 middle.1 source.1)
      hsigma (by linarith) hS hsumSmall Gsmall (Ddef.comp Glarge)
      hGsmall hDG
  have hrateEq : (theta - theta / 3) - theta / 3 = theta / 3 := by ring
  rw [hrateEq] at hcomp
  rw [cmp99SourceGeneratedNestedPhysicalGreen_transition_resolvent
    OmegaSmall OmegaLarge hM depth hspacing background budget fineSmall hsmall]
  simpa [cmp99SourceGeneratedPhysicalGreenTransitionDecayAmplitude,
    theta, c, AG, AD, S, FineSmall, FineLarge, R, Glarge, Gsmall, Ddef]
    using hcomp

end

end YangMills.RG
