/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceRegionalCoarseKernel

/-!
# Exponential decay of the physical CMP99 coarse middle transition

This file consumes the literal Green mismatch, the weighted-adjoint middle
identity and the physical fine/coarse block kernels.  It proves a fixed-rate,
volume-uniform exponential kernel bound for the complete rectangular defect
of `Q' G'^2 Q'^dagger`.
-/

namespace YangMills.RG

noncomputable section

variable {Q M j Nc : ℕ} [NeZero Q] [NeZero M] [NeZero Nc]
variable {cell : FinBox 4 Q}

/-- Explicit amplitude for one physical coarse middle operator
`Q' G'^2 Q'^dagger`. -/
noncomputable def
    cmp99OmegaSourcePhysicalOneStepCoarseMiddleDecayAmplitude
    (M : ℕ) (spacing a : ℝ) : ℝ :=
  let theta := cmp99OmegaSourcePhysicalOneStepCombesThomasRate M spacing a
  let AG := 2 / cmp99OmegaSourcePhysicalOneStepCoercivityConstant M spacing a
  let S := cmp99OmegaSiteExpSumBound (theta / 12)
  let AQ := Real.exp ((theta / 3) * (M : ℝ))
  let AQdag := (M : ℝ) ^ 2 * Real.exp ((theta / 2) * (M : ℝ))
  AQ * (AG * (AG * AQdag * S) * S) * S

set_option maxHeartbeats 1200000 in
/-- The literal physical middle operator is exponentially localized with a
fixed positive rate and a volume-independent amplitude. -/
theorem cmp99OmegaSourcePhysicalOneStepCoarseCovarianceMiddle_exponentialKernelBound
    (Seq : CMP99SourceOmegaGeometry cell j) (r : Fin (j + 2))
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground 4 (M * (2 * Q)) Nc)
    {spacing a : ℝ} (hspacing : 0 < spacing) (ha : 0 < a) :
    FinitePiLpExponentialKernelBound
      (cmp99OmegaSourcePhysicalOneStepCoarseCovarianceMiddle
        Seq r rho U hspacing ha)
      (cmp99OmegaCoarseDist (M := M) Seq r)
      (cmp99OmegaSourcePhysicalOneStepCoarseMiddleDecayAmplitude M spacing a)
      (cmp99OmegaSourcePhysicalOneStepCombesThomasRate M spacing a / 4) := by
  let theta := cmp99OmegaSourcePhysicalOneStepCombesThomasRate M spacing a
  let AG := 2 / cmp99OmegaSourcePhysicalOneStepCoercivityConstant M spacing a
  let S := cmp99OmegaSiteExpSumBound (theta / 12)
  let AQ := Real.exp ((theta / 3) * (M : ℝ))
  let AQdag := (M : ℝ) ^ 2 * Real.exp ((theta / 2) * (M : ℝ))
  let G := cmp99OmegaSourcePhysicalOneStepGreen Seq r rho U hspacing ha
  let Qop := cmp99OmegaSourcePhysicalOneStepQ Seq r rho U
  let Qdag := (cmp99OmegaSourcePhysicalOneStepTower Seq r rho U spacing).weightedAdjoint
  have htheta : 0 < theta :=
    cmp99OmegaSourcePhysicalOneStepCombesThomasRate_pos hspacing ha
  have hsigma : 0 < theta / 12 := by positivity
  have hS : 0 ≤ S := by
    dsimp [S, cmp99OmegaSiteExpSumBound]
    exact tsum_nonneg fun _ => mul_nonneg (Nat.cast_nonneg _)
      (Real.exp_pos _).le
  have hG0 : FinitePiLpTypedExponentialKernelBound G
      (cmp99OmegaSiteDist Seq r) AG theta :=
    finitePiLpTypedExponentialKernelBound_of_square
      (cmp99OmegaSourcePhysicalOneStepGreen_canonicalExponentialKernelBound
        Seq r rho U hspacing ha)
  have hGhalf : FinitePiLpTypedExponentialKernelBound G
      (cmp99OmegaSiteDist Seq r) AG (theta / 2) :=
    finitePiLpTypedExponentialKernelBound_mono_rate
      (by positivity) (by linarith) hG0
  have hQdag : FinitePiLpTypedExponentialKernelBound Qdag
      (cmp99OmegaCoarseToFineDist (M := M) Seq r)
      AQdag (theta / 2) := by
    simpa [AQdag] using finitePiLpTypedExponentialKernelBound_of_finiteRange
      (beta := (M : ℝ) ^ 2) (rate := theta / 2) (R := M)
      (by positivity) (by positivity) Qdag
      (cmp99OmegaSourcePhysicalOneStepWeightedAdjoint_finiteRange_M
        Seq r rho U spacing)
      (cmp99OmegaSourcePhysicalOneStepWeightedAdjoint_kernelBound
        Seq r rho U spacing)
  have hsumFine : ∀ target : ActiveGaugeRegion.Site
      (cmp99OmegaActiveGaugeRegion (M := M) Seq r),
      ∑ middle : ActiveGaugeRegion.Site
          (cmp99OmegaActiveGaugeRegion (M := M) Seq r),
        Real.exp (-((theta / 12) *
        (cmp99OmegaSiteDist Seq r target middle : ℝ))) ≤ S := by
    intro target
    exact cmp99OmegaSiteDist_exp_sum_le Seq r target hsigma
  have hGQdag : FinitePiLpTypedExponentialKernelBound (G.comp Qdag)
      (cmp99OmegaCoarseToFineDist (M := M) Seq r)
      (AG * AQdag * S) (5 * theta / 12) := by
    have h := finitePiLpTypedExponentialKernelBound_comp
      (cmp99OmegaSiteDist Seq r)
      (cmp99OmegaCoarseToFineDist (M := M) Seq r)
      (cmp99OmegaCoarseToFineDist (M := M) Seq r)
      (fun target middle source =>
        finBoxDist_triangle target.1 middle.1
          (cmp99OmegaCoarseRepresentative (M := M) Seq r source))
      hsigma (by linarith) hS hsumFine G Qdag hGhalf hQdag
    convert h using 1 <;> ring
  have hGfive : FinitePiLpTypedExponentialKernelBound G
      (cmp99OmegaSiteDist Seq r) AG (5 * theta / 12) :=
    finitePiLpTypedExponentialKernelBound_mono_rate
      (by positivity) (by linarith) hG0
  have hGGQdag : FinitePiLpTypedExponentialKernelBound
      (G.comp (G.comp Qdag))
      (cmp99OmegaCoarseToFineDist (M := M) Seq r)
      (AG * (AG * AQdag * S) * S) (theta / 3) := by
    have h := finitePiLpTypedExponentialKernelBound_comp
      (cmp99OmegaSiteDist Seq r)
      (cmp99OmegaCoarseToFineDist (M := M) Seq r)
      (cmp99OmegaCoarseToFineDist (M := M) Seq r)
      (fun target middle source =>
        finBoxDist_triangle target.1 middle.1
          (cmp99OmegaCoarseRepresentative (M := M) Seq r source))
      hsigma (by linarith) hS hsumFine G (G.comp Qdag) hGfive hGQdag
    convert h using 1 <;> ring
  have hQ : FinitePiLpTypedExponentialKernelBound Qop
      (cmp99OmegaFineToCoarseDist (M := M) Seq r)
      AQ (theta / 3) := by
    simpa [AQ] using finitePiLpTypedExponentialKernelBound_of_finiteRange
      (beta := 1) (rate := theta / 3) (R := M)
      (by positivity) (by positivity) Qop
      (cmp99OmegaSourcePhysicalOneStepQ_finiteRange_M Seq r rho U)
      (cmp99OmegaSourcePhysicalOneStepQ_kernelBound_one
        Seq r rho U hspacing)
  have hsumCoarse : ∀ target : ActiveGaugeRegion.Site
      (cmp99ActiveCoarseRegion (M := M) (N' := 2 * Q)
        (cmp99OmegaActiveGaugeRegion (M := M) Seq r)),
      ∑ middle : ActiveGaugeRegion.Site
          (cmp99OmegaActiveGaugeRegion (M := M) Seq r),
        Real.exp (-((theta / 12) *
        (cmp99OmegaFineToCoarseDist (M := M) Seq r target middle : ℝ))) ≤ S := by
    intro target
    exact cmp99OmegaFineToCoarseDist_exp_sum_le Seq r target hsigma
  have hFinal : FinitePiLpTypedExponentialKernelBound
      (Qop.comp (G.comp (G.comp Qdag)))
      (cmp99OmegaCoarseDist (M := M) Seq r)
      (AQ * (AG * (AG * AQdag * S) * S) * S) (theta / 4) := by
    have h := finitePiLpTypedExponentialKernelBound_comp
      (cmp99OmegaFineToCoarseDist (M := M) Seq r)
      (cmp99OmegaCoarseToFineDist (M := M) Seq r)
      (cmp99OmegaCoarseDist (M := M) Seq r)
      (fun target middle source =>
        finBoxDist_triangle
          (cmp99OmegaCoarseRepresentative (M := M) Seq r target)
          middle.1
          (cmp99OmegaCoarseRepresentative (M := M) Seq r source))
      hsigma (by linarith) hS hsumCoarse Qop (G.comp (G.comp Qdag))
      hQ hGGQdag
    convert h using 1 <;> ring
  change FinitePiLpExponentialKernelBound
    (Qop.comp (G.comp (G.comp Qdag))) _ _ _
  simpa [cmp99OmegaSourcePhysicalOneStepCoarseMiddleDecayAmplitude,
    theta, AG, S, AQ, AQdag, G, Qop, Qdag] using hFinal

/-- Explicit amplitude for the complete coarse-middle transition. -/
noncomputable def
    cmp99OmegaSourcePhysicalOneStepCoarseMiddleTransitionDecayAmplitude
    (M : ℕ) (spacing a : ℝ) : ℝ :=
  let theta := cmp99OmegaSourcePhysicalOneStepCombesThomasRate M spacing a
  let AG := 2 / cmp99OmegaSourcePhysicalOneStepCoercivityConstant M spacing a
  let AH := cmp99OmegaSourcePhysicalOneStepGreenTransitionDecayAmplitude
    M spacing a
  let S := cmp99OmegaSiteExpSumBound (theta / 12)
  let AQ := Real.exp ((theta / 4) * (M : ℝ))
  let AQdag := (M : ℝ) ^ 2 * Real.exp ((theta / 6) * (M : ℝ))
  (AQ * (AG * AH * S + AH * AG * S) * S) * AQdag * S

set_option maxHeartbeats 1200000 in
/-- C4 for the literal physical defect of `Q' G'^2 Q'^dagger` across two
different regional fine spaces and two different active coarse strata. -/
theorem cmp99OmegaSourcePhysicalOneStepCoarseMiddleTransitionDefect_exponentialKernelBound
    (Seq : CMP99SourceOmegaGeometry cell j) (r : Fin (j + 1))
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground 4 (M * (2 * Q)) Nc)
    {spacing a : ℝ} (hspacing : 0 < spacing) (ha : 0 < a) :
    FinitePiLpTypedExponentialKernelBound
      (cmp99OmegaSourcePhysicalOneStepCoarseMiddleTransitionDefect
        Seq r rho U hspacing ha)
      (cmp99OmegaCoarseTransitionDist (M := M) Seq r)
      (cmp99OmegaSourcePhysicalOneStepCoarseMiddleTransitionDecayAmplitude
        M spacing a)
      (cmp99OmegaSourcePhysicalOneStepCombesThomasRate M spacing a / 12) := by
  let theta := cmp99OmegaSourcePhysicalOneStepCombesThomasRate M spacing a
  let AG := 2 / cmp99OmegaSourcePhysicalOneStepCoercivityConstant M spacing a
  let AH := cmp99OmegaSourcePhysicalOneStepGreenTransitionDecayAmplitude
    M spacing a
  let S := cmp99OmegaSiteExpSumBound (theta / 12)
  let AQ := Real.exp ((theta / 4) * (M : ℝ))
  let AQdag := (M : ℝ) ^ 2 * Real.exp ((theta / 6) * (M : ℝ))
  let largeIndex := cmp99OmegaTransitionIndex r
  let smallIndex := cmp99OmegaTransitionNextIndex r
  let Glarge := cmp99OmegaSourcePhysicalOneStepGreen Seq
    largeIndex rho U hspacing ha
  let Gsmall := cmp99OmegaSourcePhysicalOneStepGreen Seq
    smallIndex rho U hspacing ha
  let H := Gsmall.comp (cmp99OmegaTransitionRestriction (M := M) Seq r) -
    (cmp99OmegaTransitionRestriction (M := M) Seq r).comp Glarge
  let Qsmall := cmp99OmegaSourcePhysicalOneStepQ Seq smallIndex rho U
  let QdagLarge := (cmp99OmegaSourcePhysicalOneStepTower Seq
    largeIndex rho U spacing).weightedAdjoint
  have htheta : 0 < theta :=
    cmp99OmegaSourcePhysicalOneStepCombesThomasRate_pos hspacing ha
  have hsigma : 0 < theta / 12 := by positivity
  have hS : 0 ≤ S := by
    dsimp [S, cmp99OmegaSiteExpSumBound]
    exact tsum_nonneg fun _ => mul_nonneg (Nat.cast_nonneg _)
      (Real.exp_pos _).le
  have hGsmall0 : FinitePiLpTypedExponentialKernelBound Gsmall
      (cmp99OmegaSiteDist Seq smallIndex) AG theta :=
    finitePiLpTypedExponentialKernelBound_of_square
      (cmp99OmegaSourcePhysicalOneStepGreen_canonicalExponentialKernelBound
        Seq smallIndex rho U hspacing ha)
  have hGlarge0 : FinitePiLpTypedExponentialKernelBound Glarge
      (cmp99OmegaSiteDist Seq largeIndex) AG theta :=
    finitePiLpTypedExponentialKernelBound_of_square
      (cmp99OmegaSourcePhysicalOneStepGreen_canonicalExponentialKernelBound
        Seq largeIndex rho U hspacing ha)
  have hGsmall : FinitePiLpTypedExponentialKernelBound Gsmall
      (cmp99OmegaSiteDist Seq smallIndex) AG (theta / 3) := by
    exact finitePiLpTypedExponentialKernelBound_mono_rate
      (by positivity) (by linarith) hGsmall0
  have hGlarge : FinitePiLpTypedExponentialKernelBound Glarge
      (cmp99OmegaSiteDist Seq largeIndex) AG (theta / 3) := by
    exact finitePiLpTypedExponentialKernelBound_mono_rate
      (by positivity) (by linarith) hGlarge0
  have hH : FinitePiLpTypedExponentialKernelBound H
      (cmp99OmegaTransitionSiteDist Seq r) AH (theta / 3) := by
    exact cmp99OmegaSourcePhysicalOneStepGreen_transition_exponentialKernelBound
      Seq r rho U hspacing ha
  have hsumSmall : ∀ target : ActiveGaugeRegion.Site
      (cmp99OmegaActiveGaugeRegion (M := M) Seq smallIndex),
      ∑ middle : ActiveGaugeRegion.Site
          (cmp99OmegaActiveGaugeRegion (M := M) Seq smallIndex),
        Real.exp (-((theta / 12) *
          (cmp99OmegaSiteDist Seq smallIndex target middle : ℝ))) ≤ S := by
    intro target
    exact cmp99OmegaSiteDist_exp_sum_le Seq smallIndex target hsigma
  have hsumTransition : ∀ target : ActiveGaugeRegion.Site
      (cmp99OmegaActiveGaugeRegion (M := M) Seq smallIndex),
      ∑ middle : ActiveGaugeRegion.Site
          (cmp99OmegaActiveGaugeRegion (M := M) Seq largeIndex),
        Real.exp (-((theta / 12) *
          (cmp99OmegaTransitionSiteDist Seq r target middle : ℝ))) ≤ S := by
    intro target
    have htargetBlock : blockSite M (2 * Q) target.1 ∈
        Seq.regions largeIndex := cmp99OmegaTransition_region_subset Seq r
      ((mem_cmp99OmegaActiveGaugeRegion_sites_iff
        (M := M) Seq smallIndex target.1).mp target.2)
    let targetLarge : ActiveGaugeRegion.Site
        (cmp99OmegaActiveGaugeRegion (M := M) Seq largeIndex) :=
      ⟨target.1, (mem_cmp99OmegaActiveGaugeRegion_sites_iff
        (M := M) Seq largeIndex target.1).mpr htargetBlock⟩
    simpa [S, cmp99OmegaTransitionSiteDist, cmp99OmegaSiteDist, targetLarge]
      using cmp99OmegaSiteDist_exp_sum_le Seq largeIndex targetLarge hsigma
  have hGsH : FinitePiLpTypedExponentialKernelBound (Gsmall.comp H)
      (cmp99OmegaTransitionSiteDist Seq r) (AG * AH * S) (theta / 4) := by
    have h := finitePiLpTypedExponentialKernelBound_comp
      (cmp99OmegaSiteDist Seq smallIndex)
      (cmp99OmegaTransitionSiteDist Seq r)
      (cmp99OmegaTransitionSiteDist Seq r)
      (fun target middle source =>
        finBoxDist_triangle target.1 middle.1 source.1)
      hsigma (by linarith) hS hsumSmall Gsmall H hGsmall hH
    convert h using 1 <;> ring
  have hHGl : FinitePiLpTypedExponentialKernelBound (H.comp Glarge)
      (cmp99OmegaTransitionSiteDist Seq r) (AH * AG * S) (theta / 4) := by
    have h := finitePiLpTypedExponentialKernelBound_comp
      (cmp99OmegaTransitionSiteDist Seq r)
      (cmp99OmegaSiteDist Seq largeIndex)
      (cmp99OmegaTransitionSiteDist Seq r)
      (fun target middle source =>
        finBoxDist_triangle target.1 middle.1 source.1)
      hsigma (by linarith) hS hsumTransition H Glarge hH hGlarge
    convert h using 1 <;> ring
  have hInner : FinitePiLpTypedExponentialKernelBound
      (Gsmall.comp H + H.comp Glarge)
      (cmp99OmegaTransitionSiteDist Seq r)
      (AG * AH * S + AH * AG * S) (theta / 4) :=
    finitePiLpTypedExponentialKernelBound_add hGsH hHGl
  have hQsmall : FinitePiLpTypedExponentialKernelBound Qsmall
      (cmp99OmegaFineToCoarseDist (M := M) Seq smallIndex)
      AQ (theta / 4) := by
    simpa [AQ] using finitePiLpTypedExponentialKernelBound_of_finiteRange
      (beta := 1) (rate := theta / 4) (R := M)
      (by positivity) (by positivity) Qsmall
      (cmp99OmegaSourcePhysicalOneStepQ_finiteRange_M
        Seq smallIndex rho U)
      (cmp99OmegaSourcePhysicalOneStepQ_kernelBound_one
        Seq smallIndex rho U hspacing)
  have hsumCoarseSmall : ∀ target,
      ∑ middle, Real.exp (-((theta / 12) *
        (cmp99OmegaFineToCoarseDist (M := M) Seq smallIndex
          target middle : ℝ))) ≤ S := by
    intro target
    exact cmp99OmegaFineToCoarseDist_exp_sum_le Seq smallIndex target hsigma
  have hQInner : FinitePiLpTypedExponentialKernelBound
      (Qsmall.comp (Gsmall.comp H + H.comp Glarge))
      (cmp99OmegaCoarseToTransitionFineDist (M := M) Seq r)
      (AQ * (AG * AH * S + AH * AG * S) * S) (theta / 6) := by
    have h := finitePiLpTypedExponentialKernelBound_comp
      (cmp99OmegaFineToCoarseDist (M := M) Seq smallIndex)
      (cmp99OmegaTransitionSiteDist Seq r)
      (cmp99OmegaCoarseToTransitionFineDist (M := M) Seq r)
      (fun target middle source =>
        finBoxDist_triangle
          (cmp99OmegaCoarseRepresentative (M := M) Seq smallIndex target)
          middle.1 source.1)
      hsigma (by linarith) hS hsumCoarseSmall Qsmall
      (Gsmall.comp H + H.comp Glarge) hQsmall hInner
    convert h using 1 <;> ring
  have hQdag : FinitePiLpTypedExponentialKernelBound QdagLarge
      (cmp99OmegaCoarseToFineDist (M := M) Seq largeIndex)
      AQdag (theta / 6) := by
    simpa [AQdag] using finitePiLpTypedExponentialKernelBound_of_finiteRange
      (beta := (M : ℝ) ^ 2) (rate := theta / 6) (R := M)
      (by positivity) (by positivity) QdagLarge
      (cmp99OmegaSourcePhysicalOneStepWeightedAdjoint_finiteRange_M
        Seq largeIndex rho U spacing)
      (cmp99OmegaSourcePhysicalOneStepWeightedAdjoint_kernelBound
        Seq largeIndex rho U spacing)
  have hsumCoarseTransition : ∀ target,
      ∑ middle, Real.exp (-((theta / 12) *
        (cmp99OmegaCoarseToTransitionFineDist (M := M) Seq r
          target middle : ℝ))) ≤ S := by
    intro target
    exact cmp99OmegaCoarseTransitionFine_exp_sum_le Seq r target hsigma
  have hFinal : FinitePiLpTypedExponentialKernelBound
      ((Qsmall.comp (Gsmall.comp H + H.comp Glarge)).comp QdagLarge)
      (cmp99OmegaCoarseTransitionDist (M := M) Seq r)
      ((AQ * (AG * AH * S + AH * AG * S) * S) * AQdag * S)
      (theta / 12) := by
    have h := finitePiLpTypedExponentialKernelBound_comp
      (cmp99OmegaCoarseToTransitionFineDist (M := M) Seq r)
      (cmp99OmegaCoarseToFineDist (M := M) Seq largeIndex)
      (cmp99OmegaCoarseTransitionDist (M := M) Seq r)
      (fun target middle source =>
        finBoxDist_triangle
          (cmp99OmegaCoarseRepresentative (M := M) Seq smallIndex target)
          middle.1
          (cmp99OmegaCoarseRepresentative (M := M) Seq largeIndex source))
      hsigma (by linarith) hS hsumCoarseTransition
      (Qsmall.comp (Gsmall.comp H + H.comp Glarge)) QdagLarge
      hQInner hQdag
    convert h using 1 <;> ring
  have hneg := finitePiLpTypedExponentialKernelBound_neg hFinal
  rw [cmp99OmegaSourcePhysicalOneStepCoarseMiddleTransitionDefect_eq_greenMismatch]
  simpa [cmp99OmegaSourcePhysicalOneStepCoarseMiddleTransitionDecayAmplitude,
    theta, AG, AH, S, AQ, AQdag, largeIndex, smallIndex, Glarge, Gsmall,
    H, Qsmall, QdagLarge, ContinuousLinearMap.comp_assoc] using hneg

end

end YangMills.RG
