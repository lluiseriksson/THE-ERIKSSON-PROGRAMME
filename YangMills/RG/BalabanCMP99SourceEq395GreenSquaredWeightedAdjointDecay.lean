/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceEq395GreenWeightedAdjointDecay

/-!
# Fixed-rate decay of the right half of the CMP99 global middle

This module composes the generated physical weighted synthesis with two
Green kernels.  Two volume-uniform shell sums are spent, while one half of
the original Combes--Thomas rate remains.
-/

namespace YangMills.RG
open YangMills Matrix
open scoped Matrix.Norms.L2Operator RealInnerProductSpace
noncomputable section

variable {M Nc Q : ℕ} [NeZero M] [NeZero Nc] [NeZero Q]

/-- Explicit amplitude of `G^2 W` at half the generated Green rate. -/
noncomputable def cmp99Eq395GeneratedGreenSquaredWeightedAdjointAmplitude
    (M depth : ℕ) (spacing epsilon : ℝ) : ℝ :=
  let theta := cmp99SourceGeneratedCombesThomasRate
    4 M depth spacing epsilon
  let sigma := theta / 4
  let S := cmp99OmegaSiteExpSumBound sigma
  let R := M ^ (depth + 1) - 1
  let AW := cmp99SourceGeneratedWeightedAdjointNormBound M depth *
    Real.exp (theta * (R : ℝ))
  let AG := 2 / cmp99SourceGeneratedCoercivity
    4 M (depth + 1) spacing epsilon
  AG * (AG * AW * S) * S

noncomputable def cmp99Eq395GeneratedGreenSquaredWeightedAdjoint
    (Omega : ActiveGaugeRegion 4 (2 * Q))
    (hM : 2 ≤ M) (depth : ℕ)
    {spacing epsilon : ℝ} (hspacing : 0 < spacing)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 M Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff 4 M (depth + 1)
      spacing epsilon < 1) := by
  let Omega' := cmp99IteratedLiftActiveRegion (M := M) Omega (depth + 1)
  let G := cmp99SourceGeneratedPhysicalGreen (show 2 ≤ 4 by norm_num) hM
    Omega depth hspacing background budget fineSmall hsmall
  let GW := cmp99Eq395GeneratedGreenWeightedAdjoint Omega hM depth hspacing
    background budget fineSmall hsmall
  exact G.comp GW

noncomputable def cmp99Eq395GeneratedGreenSquaredWeightedAdjointKernelData
    (Omega : ActiveGaugeRegion 4 (2 * Q))
    (hM : 2 ≤ M) (depth : ℕ)
    {spacing epsilon : ℝ} (hspacing : 0 < spacing)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 M Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff 4 M (depth + 1)
      spacing epsilon < 1) : CMP99Eq395TypedKernelData Nc := by
  let regions := cmp99SourceIteratedLiftActiveRegionChain
    (M := M) Omega (depth + 1)
  let Omega' := cmp99IteratedLiftActiveRegion (M := M) Omega (depth + 1)
  exact {
    source := regions.terminalSite
    target := ActiveGaugeRegion.Site Omega'
    operator := cmp99Eq395GeneratedGreenSquaredWeightedAdjoint Omega hM depth
      hspacing background budget fineSmall hsmall
    dist := cmp99Eq395GeneratedGreenWeightedAdjointDist (M := M) Omega depth
  }

set_option maxRecDepth 4000
set_option maxHeartbeats 5000000 in
/-- The literal generated operator `G^2 W` has a fixed-rate rectangular
kernel bound independent of the active-region cardinality. -/
theorem cmp99Eq395GeneratedGreenSquaredWeightedAdjoint_exponentialKernelBound
    (Omega : ActiveGaugeRegion 4 (2 * Q))
    (hM : 2 ≤ M) (depth : ℕ)
    {spacing epsilon : ℝ} (hspacing : 0 < spacing)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 M Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff 4 M (depth + 1)
      spacing epsilon < 1) :
    (cmp99Eq395GeneratedGreenSquaredWeightedAdjointKernelData Omega hM depth
      hspacing background budget fineSmall hsmall).ExponentialKernelBound
      (cmp99Eq395GeneratedGreenSquaredWeightedAdjointAmplitude
        M depth spacing epsilon)
      (cmp99SourceGeneratedCombesThomasRate
        4 M depth spacing epsilon / 2) := by
  let regions := cmp99SourceIteratedLiftActiveRegionChain
    (M := M) Omega (depth + 1)
  let Omega' := cmp99IteratedLiftActiveRegion (M := M) Omega (depth + 1)
  let W := regions.physicalWeightedAdjoint (show 2 ≤ 4 by norm_num) hM
    (matrixSUNAdjointModel Nc) spacing epsilon background
    budget.toRadiusChain fineSmall
  let G := cmp99SourceGeneratedPhysicalGreen (show 2 ≤ 4 by norm_num) hM
    Omega depth hspacing background budget fineSmall hsmall
  let theta := cmp99SourceGeneratedCombesThomasRate
    4 M depth spacing epsilon
  let sigma := theta / 4
  let S := cmp99OmegaSiteExpSumBound sigma
  let R := M ^ (depth + 1) - 1
  let AW := cmp99SourceGeneratedWeightedAdjointNormBound M depth *
    Real.exp (theta * (R : ℝ))
  let AG := 2 / cmp99SourceGeneratedCoercivity
    4 M (depth + 1) spacing epsilon
  have htheta : 0 < theta :=
    cmp99SourceGeneratedCombesThomasRate_pos
      4 M depth hspacing hsmall
  have hsigma : 0 < sigma := by dsimp [sigma]; positivity
  have hS : 0 ≤ S := by
    dsimp [S, cmp99OmegaSiteExpSumBound]
    exact tsum_nonneg fun _ => mul_nonneg (Nat.cast_nonneg _)
      (Real.exp_pos _).le
  have hG0 : FinitePiLpTypedExponentialKernelBound G
      (fun target source => finBoxDist target.1 source.1) AG theta := by
    simpa [G, AG] using finitePiLpTypedExponentialKernelBound_of_square
      (cmp99SourceGeneratedPhysicalGreen_canonicalExponentialKernelBound
        (show 2 ≤ 4 by norm_num) hM Omega depth hspacing background budget
          fineSmall hsmall)
  have hGthree : FinitePiLpTypedExponentialKernelBound G
      (fun target source => finBoxDist target.1 source.1) AG
      (3 * theta / 4) :=
    finitePiLpTypedExponentialKernelBound_mono_rate
      (by positivity) (by linarith) hG0
  have hsumFine : ∀ target : ActiveGaugeRegion.Site Omega',
      ∑ middle : ActiveGaugeRegion.Site Omega',
        Real.exp (-(sigma * (finBoxDist target.1 middle.1 : ℝ))) ≤ S := by
    intro target
    exact activeGaugeRegion_finBoxDist_exp_sum_le Omega' target hsigma
  have hGW : FinitePiLpTypedExponentialKernelBound (G.comp W)
      (fun target source => finBoxDist target.1
        (regions.terminalRepresentative source).1)
      (AG * AW * S) (3 * theta / 4) := by
    have h := cmp99Eq395GeneratedGreenWeightedAdjoint_exponentialKernelBound
      Omega hM depth hspacing background budget fineSmall hsmall
    change FinitePiLpTypedExponentialKernelBound (G.comp W)
      (fun target source => finBoxDist target.1
        (regions.terminalRepresentative source).1)
      (cmp99Eq395GeneratedGreenWeightedAdjointAmplitude
        M depth spacing epsilon) (3 * theta / 4) at h
    have hamp : cmp99Eq395GeneratedGreenWeightedAdjointAmplitude
        M depth spacing epsilon = AG * AW * S := rfl
    simpa only [hamp] using h
  have hGGW := finitePiLpTypedExponentialKernelBound_comp
    (ι := regions.terminalSite)
    (κ := ActiveGaugeRegion.Site Omega')
    (ν := ActiveGaugeRegion.Site Omega')
    (g := SUNLieCoord Nc)
    (A := AG) (B := AG * AW * S) (rate := 3 * theta / 4)
    (sigma := sigma) (S := S)
    (fun target middle => finBoxDist target.1 middle.1)
    (fun middle source => finBoxDist middle.1
      (regions.terminalRepresentative source).1)
    (fun target source => finBoxDist target.1
      (regions.terminalRepresentative source).1)
    (fun target middle source => finBoxDist_triangle target.1 middle.1
      (regions.terminalRepresentative source).1)
    hsigma (by dsimp [sigma]; linarith) hS hsumFine G (G.comp W)
    hGthree hGW
  change FinitePiLpTypedExponentialKernelBound (G.comp (G.comp W))
    (fun target source => finBoxDist target.1
      (regions.terminalRepresentative source).1)
    (cmp99Eq395GeneratedGreenSquaredWeightedAdjointAmplitude
      M depth spacing epsilon) (theta / 2)
  have hamp : cmp99Eq395GeneratedGreenSquaredWeightedAdjointAmplitude
      M depth spacing epsilon = AG * (AG * AW * S) * S := rfl
  rw [hamp]
  convert hGGW using 1 <;> ring

end
end YangMills.RG
