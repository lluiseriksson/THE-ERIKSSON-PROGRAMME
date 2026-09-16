/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceEq395GlobalRegionalMiddleDecay

/-!
# Exponential decay of the CMP99 full-to-Pi4 middle defect

The rectangular physical formula exposed by the preceding module is composed
at one fixed generated Combes--Thomas rate.  The resulting amplitude is
independent of the ambient torus volume.
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

/-- Fine-representative distance between a regional terminal coordinate and
a full-torus terminal coordinate. -/
def cmp99Eq395PhysicalGlobalRegionalMiddleDist
    (D : CMP99SourceDependentOmegaGeometry
      (FinBox 4 (2 * Q)) j ScaleSite Scaled
      (cmp99SourceTildePiLargeBlocks cell 3)
      (cmp99SourceTildePiLargeBlocks cell 4) dist gap)
    (hpi5 : D.fineRegion (cmp99OmegaZeroIndex j) ⊆
      cmp99SourceTildePiLargeBlocks cell 5) (depth : ℕ) :=
  let OmegaSmall := D.operatorCoarseRegion hpi5 (cmp99OmegaPi4Index j)
  let OmegaLarge := cmp99Eq395FullCoarseRegion (Q := Q)
  let regionsSmall := cmp99SourceIteratedLiftActiveRegionChain (M := M)
    OmegaSmall (depth + 1)
  let regionsLarge := cmp99SourceIteratedLiftActiveRegionChain (M := M)
    OmegaLarge (depth + 1)
  fun (target : regionsSmall.terminalSite) (source : regionsLarge.terminalSite) =>
    finBoxDist (regionsSmall.terminalRepresentative target).1
      (regionsLarge.terminalRepresentative source).1

/-- Explicit volume-independent amplitude for the complete full-to-`Pi^4`
middle defect. -/
noncomputable def cmp99Eq395PhysicalGlobalRegionalMiddleDecayAmplitude
    (M depth : ℕ) (spacing epsilon : ℝ) : ℝ :=
  let theta := cmp99SourceGeneratedCombesThomasRate
    4 M depth spacing epsilon
  let S := cmp99OmegaSiteExpSumBound (theta / 12)
  let R := M ^ (depth + 1) - 1
  let AW := cmp99SourceGeneratedWeightedAdjointNormBound M depth *
    Real.exp (theta * (R : ℝ))
  let AG := 2 / cmp99SourceGeneratedCoercivity
    4 M (depth + 1) spacing epsilon
  let AH := cmp99SourceGeneratedPhysicalGreenTransitionDecayAmplitude
    M depth spacing epsilon
  let qscale := cmp99Eq395GeneratedQprimeScale M depth spacing
  ((|qscale| * AW) * (AG * AH * S + AH * AG * S) * S) * AW * S

set_option maxRecDepth 5000
set_option synthInstance.maxHeartbeats 3000000 in
set_option maxHeartbeats 10000000 in
/- The complete source-specific full-to-`Pi^4` middle transport has a fixed
positive exponential rate and an amplitude independent of the ambient
volume. -/
theorem cmp99Eq395PhysicalGlobalRegionalMiddleGreenTransportPhysical_exponentialKernelBound
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
    FinitePiLpTypedExponentialKernelBound
      (D.cmp99Eq395PhysicalGlobalRegionalMiddleGreenTransportPhysical hpi5 hM
        depth hspacing background budget fineSmall hsmall)
      (D.cmp99Eq395PhysicalGlobalRegionalMiddleDist hpi5 depth)
      (cmp99Eq395PhysicalGlobalRegionalMiddleDecayAmplitude
        M depth spacing epsilon)
      (cmp99SourceGeneratedCombesThomasRate
        4 M depth spacing epsilon / 12) := by
  let OmegaSmall := D.operatorCoarseRegion hpi5 (cmp99OmegaPi4Index j)
  let OmegaLarge := cmp99Eq395FullCoarseRegion (Q := Q)
  let FineSmall := cmp99IteratedLiftActiveRegion (M := M) OmegaSmall
    (depth + 1)
  let FineLarge := cmp99IteratedLiftActiveRegion (M := M) OmegaLarge
    (depth + 1)
  let regionsSmall := cmp99SourceIteratedLiftActiveRegionChain (M := M)
    OmegaSmall (depth + 1)
  let regionsLarge := cmp99SourceIteratedLiftActiveRegionChain (M := M)
    OmegaLarge (depth + 1)
  let Wsmall := regionsSmall.physicalWeightedAdjoint
    (show 2 ≤ 4 by norm_num) hM (matrixSUNAdjointModel Nc) spacing epsilon
    background budget.toRadiusChain fineSmall
  let Wlarge := regionsLarge.physicalWeightedAdjoint
    (show 2 ≤ 4 by norm_num) hM (matrixSUNAdjointModel Nc) spacing epsilon
    background budget.toRadiusChain fineSmall
  let Gsmall := cmp99SourceGeneratedPhysicalGreen (show 2 ≤ 4 by norm_num) hM
    OmegaSmall depth hspacing background budget fineSmall hsmall
  let Glarge := cmp99SourceGeneratedPhysicalGreen (show 2 ≤ 4 by norm_num) hM
    OmegaLarge depth hspacing background budget fineSmall hsmall
  let H := cmp99SourceGeneratedNestedPhysicalGreenTransition OmegaSmall
    OmegaLarge hM depth hspacing background budget fineSmall hsmall
  let Inner := Gsmall.comp H + H.comp Glarge
  let theta := cmp99SourceGeneratedCombesThomasRate
    4 M depth spacing epsilon
  let sigma := theta / 12
  let S := cmp99OmegaSiteExpSumBound sigma
  let R := M ^ (depth + 1) - 1
  let AW := cmp99SourceGeneratedWeightedAdjointNormBound M depth *
    Real.exp (theta * (R : ℝ))
  let AG := 2 / cmp99SourceGeneratedCoercivity
    4 M (depth + 1) spacing epsilon
  let AH := cmp99SourceGeneratedPhysicalGreenTransitionDecayAmplitude
    M depth spacing epsilon
  let qscale := cmp99Eq395GeneratedQprimeScale M depth spacing
  have hFineSub : FineSmall.sites ⊆ FineLarge.sites :=
    cmp99IteratedLiftActiveRegion_sites_mono
      (D.cmp99Eq395PhysicalRegion_subset_full hpi5) (depth + 1)
  have htheta : 0 < theta :=
    cmp99SourceGeneratedCombesThomasRate_pos 4 M depth hspacing hsmall
  have hsigma : 0 < sigma := by dsimp [sigma]; positivity
  have hS : 0 ≤ S := by
    dsimp [S, cmp99OmegaSiteExpSumBound]
    exact tsum_nonneg fun _ => mul_nonneg (Nat.cast_nonneg _)
      (Real.exp_pos _).le
  have hGsmall0 : FinitePiLpTypedExponentialKernelBound Gsmall
      (fun x y : ActiveGaugeRegion.Site FineSmall => finBoxDist x.1 y.1)
      AG theta := by
    exact finitePiLpTypedExponentialKernelBound_of_square
      (cmp99SourceGeneratedPhysicalGreen_canonicalExponentialKernelBound
        (show 2 ≤ 4 by norm_num) hM OmegaSmall depth hspacing background
        budget fineSmall hsmall)
  have hGlarge0 : FinitePiLpTypedExponentialKernelBound Glarge
      (fun x y : ActiveGaugeRegion.Site FineLarge => finBoxDist x.1 y.1)
      AG theta := by
    exact finitePiLpTypedExponentialKernelBound_of_square
      (cmp99SourceGeneratedPhysicalGreen_canonicalExponentialKernelBound
        (show 2 ≤ 4 by norm_num) hM OmegaLarge depth hspacing background
        budget fineSmall hsmall)
  have hGsmall : FinitePiLpTypedExponentialKernelBound Gsmall
      (fun x y : ActiveGaugeRegion.Site FineSmall => finBoxDist x.1 y.1)
      AG (theta / 3) :=
    finitePiLpTypedExponentialKernelBound_mono_rate
      (by positivity) (by linarith) hGsmall0
  have hGlarge : FinitePiLpTypedExponentialKernelBound Glarge
      (fun x y : ActiveGaugeRegion.Site FineLarge => finBoxDist x.1 y.1)
      AG (theta / 3) :=
    finitePiLpTypedExponentialKernelBound_mono_rate
      (by positivity) (by linarith) hGlarge0
  have hH : FinitePiLpTypedExponentialKernelBound H
      (fun target : ActiveGaugeRegion.Site FineSmall =>
        fun source : ActiveGaugeRegion.Site FineLarge =>
          finBoxDist target.1 source.1) AH (theta / 3) := by
    exact cmp99SourceGeneratedNestedPhysicalGreenTransition_exponentialKernelBound
      OmegaSmall OmegaLarge (D.cmp99Eq395PhysicalRegion_subset_full hpi5)
      hM depth hspacing background budget fineSmall hsmall
  have hsumSmall : ∀ target : ActiveGaugeRegion.Site FineSmall,
      ∑ middle : ActiveGaugeRegion.Site FineSmall,
        Real.exp (-(sigma * (finBoxDist target.1 middle.1 : ℝ))) ≤ S := by
    intro target
    exact activeGaugeRegion_finBoxDist_exp_sum_le FineSmall target hsigma
  have hsumLargeFromSmall : ∀ target : ActiveGaugeRegion.Site FineSmall,
      ∑ middle : ActiveGaugeRegion.Site FineLarge,
        Real.exp (-(sigma * (finBoxDist target.1 middle.1 : ℝ))) ≤ S := by
    intro target
    let targetLarge : ActiveGaugeRegion.Site FineLarge :=
      ⟨target.1, hFineSub target.2⟩
    simpa [targetLarge] using
      activeGaugeRegion_finBoxDist_exp_sum_le FineLarge targetLarge hsigma
  have hGsH : FinitePiLpTypedExponentialKernelBound (Gsmall.comp H)
      (fun target : ActiveGaugeRegion.Site FineSmall =>
        fun source : ActiveGaugeRegion.Site FineLarge =>
          finBoxDist target.1 source.1)
      (AG * AH * S) (theta / 4) := by
    have h := finitePiLpTypedExponentialKernelBound_comp
      (fun x y : ActiveGaugeRegion.Site FineSmall => finBoxDist x.1 y.1)
      (fun target : ActiveGaugeRegion.Site FineSmall =>
        fun source : ActiveGaugeRegion.Site FineLarge =>
          finBoxDist target.1 source.1)
      (fun target : ActiveGaugeRegion.Site FineSmall =>
        fun source : ActiveGaugeRegion.Site FineLarge =>
          finBoxDist target.1 source.1)
      (fun target middle source => finBoxDist_triangle
        target.1 middle.1 source.1)
      hsigma (by dsimp [sigma]; linarith) hS hsumSmall Gsmall H hGsmall hH
    convert h using 1 <;> ring
  have hHGl : FinitePiLpTypedExponentialKernelBound (H.comp Glarge)
      (fun target : ActiveGaugeRegion.Site FineSmall =>
        fun source : ActiveGaugeRegion.Site FineLarge =>
          finBoxDist target.1 source.1)
      (AH * AG * S) (theta / 4) := by
    have h := finitePiLpTypedExponentialKernelBound_comp
      (fun target : ActiveGaugeRegion.Site FineSmall =>
        fun middle : ActiveGaugeRegion.Site FineLarge =>
          finBoxDist target.1 middle.1)
      (fun x y : ActiveGaugeRegion.Site FineLarge => finBoxDist x.1 y.1)
      (fun target : ActiveGaugeRegion.Site FineSmall =>
        fun source : ActiveGaugeRegion.Site FineLarge =>
          finBoxDist target.1 source.1)
      (fun target middle source => finBoxDist_triangle
        target.1 middle.1 source.1)
      hsigma (by dsimp [sigma]; linarith) hS hsumLargeFromSmall
      H Glarge hH hGlarge
    convert h using 1 <;> ring
  have hInner : FinitePiLpTypedExponentialKernelBound Inner
      (fun target : ActiveGaugeRegion.Site FineSmall =>
        fun source : ActiveGaugeRegion.Site FineLarge =>
          finBoxDist target.1 source.1)
      (AG * AH * S + AH * AG * S) (theta / 4) :=
    finitePiLpTypedExponentialKernelBound_add hGsH hHGl
  have hWsmall0 : FinitePiLpTypedExponentialKernelBound Wsmall
      (fun target source => finBoxDist target.1
        (regionsSmall.terminalRepresentative source).1) AW theta := by
    have h := cmp99Eq395GeneratedPhysicalWeightedAdjoint_exponentialKernelBound
      OmegaSmall hM depth hspacing htheta background budget fineSmall
    change FinitePiLpTypedExponentialKernelBound Wsmall _
      (cmp99SourceGeneratedWeightedAdjointNormBound M depth *
        Real.exp (theta * ((M ^ (depth + 1) - 1 : ℕ) : ℝ))) theta at h
    simpa only [AW, R] using h
  have hWsmallAdj0 : FinitePiLpTypedExponentialKernelBound Wsmall.adjoint
      (fun target source => finBoxDist source.1
        (regionsSmall.terminalRepresentative target).1) AW theta :=
    finitePiLpTypedExponentialKernelBound_adjoint _ Wsmall hWsmall0
  have hWsmallAdj : FinitePiLpTypedExponentialKernelBound Wsmall.adjoint
      (fun target source => finBoxDist source.1
        (regionsSmall.terminalRepresentative target).1) AW (theta / 4) :=
    finitePiLpTypedExponentialKernelBound_mono_rate
      (by positivity) (by linarith) hWsmallAdj0
  have hQsmall : FinitePiLpTypedExponentialKernelBound
      (qscale • Wsmall.adjoint)
      (fun target source => finBoxDist source.1
        (regionsSmall.terminalRepresentative target).1)
      (|qscale| * AW) (theta / 4) :=
    finitePiLpTypedExponentialKernelBound_smul qscale hWsmallAdj
  have hsumTerminalSmall : ∀ target : regionsSmall.terminalSite,
      ∑ middle : ActiveGaugeRegion.Site FineSmall,
        Real.exp (-(sigma * (finBoxDist middle.1
          (regionsSmall.terminalRepresentative target).1 : ℝ))) ≤ S := by
    intro target
    simpa [finBoxDist_comm] using
      activeGaugeRegion_finBoxDist_exp_sum_le FineSmall
        (regionsSmall.terminalRepresentative target) hsigma
  have hQInner : FinitePiLpTypedExponentialKernelBound
      ((qscale • Wsmall.adjoint).comp Inner)
      (fun target : regionsSmall.terminalSite =>
        fun source : ActiveGaugeRegion.Site FineLarge =>
          finBoxDist (regionsSmall.terminalRepresentative target).1 source.1)
      ((|qscale| * AW) * (AG * AH * S + AH * AG * S) * S)
      (theta / 6) := by
    have h := finitePiLpTypedExponentialKernelBound_comp
      (fun target : regionsSmall.terminalSite =>
        fun middle : ActiveGaugeRegion.Site FineSmall =>
          finBoxDist middle.1
            (regionsSmall.terminalRepresentative target).1)
      (fun target : ActiveGaugeRegion.Site FineSmall =>
        fun source : ActiveGaugeRegion.Site FineLarge =>
          finBoxDist target.1 source.1)
      (fun target : regionsSmall.terminalSite =>
        fun source : ActiveGaugeRegion.Site FineLarge =>
          finBoxDist (regionsSmall.terminalRepresentative target).1 source.1)
      (fun target middle source => by
        simpa [finBoxDist_comm] using finBoxDist_triangle
          (regionsSmall.terminalRepresentative target).1 middle.1 source.1)
      hsigma (by dsimp [sigma]; linarith) hS hsumTerminalSmall
      (qscale • Wsmall.adjoint) Inner hQsmall hInner
    convert h using 1 <;> ring
  have hWlarge0 : FinitePiLpTypedExponentialKernelBound Wlarge
      (fun target source => finBoxDist target.1
        (regionsLarge.terminalRepresentative source).1) AW theta := by
    have h := cmp99Eq395GeneratedPhysicalWeightedAdjoint_exponentialKernelBound
      OmegaLarge hM depth hspacing htheta background budget fineSmall
    change FinitePiLpTypedExponentialKernelBound Wlarge _
      (cmp99SourceGeneratedWeightedAdjointNormBound M depth *
        Real.exp (theta * ((M ^ (depth + 1) - 1 : ℕ) : ℝ))) theta at h
    simpa only [AW, R] using h
  have hWlarge : FinitePiLpTypedExponentialKernelBound Wlarge
      (fun target source => finBoxDist target.1
        (regionsLarge.terminalRepresentative source).1) AW (theta / 6) :=
    finitePiLpTypedExponentialKernelBound_mono_rate
      (by positivity) (by linarith) hWlarge0
  have hsumTerminalTransition : ∀ target : regionsSmall.terminalSite,
      ∑ middle : ActiveGaugeRegion.Site FineLarge,
        Real.exp (-(sigma * (finBoxDist
          (regionsSmall.terminalRepresentative target).1 middle.1 : ℝ))) ≤ S := by
    intro target
    let targetLarge : ActiveGaugeRegion.Site FineLarge :=
      ⟨(regionsSmall.terminalRepresentative target).1,
        hFineSub (regionsSmall.terminalRepresentative target).2⟩
    simpa [targetLarge] using
      activeGaugeRegion_finBoxDist_exp_sum_le FineLarge targetLarge hsigma
  have hFinal : FinitePiLpTypedExponentialKernelBound
      (((qscale • Wsmall.adjoint).comp Inner).comp Wlarge)
      (fun target : regionsSmall.terminalSite =>
        fun source : regionsLarge.terminalSite =>
          finBoxDist (regionsSmall.terminalRepresentative target).1
            (regionsLarge.terminalRepresentative source).1)
      (((|qscale| * AW) * (AG * AH * S + AH * AG * S) * S) * AW * S)
      (theta / 12) := by
    have h := finitePiLpTypedExponentialKernelBound_comp
      (fun target : regionsSmall.terminalSite =>
        fun middle : ActiveGaugeRegion.Site FineLarge =>
          finBoxDist (regionsSmall.terminalRepresentative target).1 middle.1)
      (fun middle : ActiveGaugeRegion.Site FineLarge =>
        fun source : regionsLarge.terminalSite =>
          finBoxDist middle.1 (regionsLarge.terminalRepresentative source).1)
      (fun target : regionsSmall.terminalSite =>
        fun source : regionsLarge.terminalSite =>
          finBoxDist (regionsSmall.terminalRepresentative target).1
            (regionsLarge.terminalRepresentative source).1)
      (fun target middle source => finBoxDist_triangle
        (regionsSmall.terminalRepresentative target).1 middle.1
        (regionsLarge.terminalRepresentative source).1)
      hsigma (by dsimp [sigma]; linarith) hS hsumTerminalTransition
      ((qscale • Wsmall.adjoint).comp Inner) Wlarge hQInner hWlarge
    convert h using 1 <;> ring
  have hneg := finitePiLpTypedExponentialKernelBound_neg hFinal
  change FinitePiLpTypedExponentialKernelBound
    (-(((qscale • Wsmall.adjoint).comp Inner).comp Wlarge))
    (D.cmp99Eq395PhysicalGlobalRegionalMiddleDist hpi5 depth)
    (cmp99Eq395PhysicalGlobalRegionalMiddleDecayAmplitude
      M depth spacing epsilon) (theta / 12)
  simpa [cmp99Eq395PhysicalGlobalRegionalMiddleGreenTransportPhysical,
    cmp99Eq395PhysicalGlobalRegionalMiddleDist,
    cmp99Eq395PhysicalGlobalRegionalMiddleDecayAmplitude,
    OmegaSmall, OmegaLarge, regionsSmall, regionsLarge, FineSmall, FineLarge,
    Wsmall, Wlarge, Gsmall, Glarge, H, Inner, theta, sigma, S, R, AW, AG,
    AH, qscale, ContinuousLinearMap.comp_assoc] using hneg

set_option maxHeartbeats 4000000 in
/- The same fixed-rate bound holds for the original second middle defect in
its literal generated terminal coordinates. -/
theorem cmp99Eq395PhysicalGlobalRegionalMiddleDefectTerminalCoordinates_exponentialKernelBound
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
    FinitePiLpTypedExponentialKernelBound
      (D.cmp99Eq395PhysicalGlobalRegionalMiddleDefectTerminalCoordinates hpi5 hM
        depth hspacing background budget fineSmall hsmall)
      (D.cmp99Eq395PhysicalGlobalRegionalMiddleDist hpi5 depth)
      (cmp99Eq395PhysicalGlobalRegionalMiddleDecayAmplitude
        M depth spacing epsilon)
      (cmp99SourceGeneratedCombesThomasRate
        4 M depth spacing epsilon / 12) := by
  rw [D.cmp99Eq395PhysicalGlobalRegionalMiddleDefectTerminalCoordinates_eq_physical]
  exact D.cmp99Eq395PhysicalGlobalRegionalMiddleGreenTransportPhysical_exponentialKernelBound
    hpi5 hM depth hspacing background budget fineSmall hsmall

end CMP99SourceDependentOmegaGeometry

end

end YangMills.RG
