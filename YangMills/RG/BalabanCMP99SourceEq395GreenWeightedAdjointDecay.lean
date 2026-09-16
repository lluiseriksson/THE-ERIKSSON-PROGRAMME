/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceEq395WeightedAdjointDecay
import YangMills.RG.BalabanCMP99SourceGeneratedCombesThomas
import YangMills.RG.BalabanCMP99SourceGeneratedGreenTransitionDecay

/-! # Fixed-rate decay of `G W` in the CMP99 global middle -/

namespace YangMills.RG
open YangMills Matrix
open scoped Matrix.Norms.L2Operator RealInnerProductSpace
noncomputable section

variable {M Nc Q : ℕ} [NeZero M] [NeZero Nc] [NeZero Q]

/-- A rectangular physical kernel together with its endpoint types and
metric.  Keeping these data in one package prevents repeated normalization
of the recursively generated lattice size. -/
structure CMP99Eq395TypedKernelData (Nc : ℕ) [NeZero Nc] where
  source : Type
  target : Type
  [sourceFintype : Fintype source]
  [sourceDecidableEq : DecidableEq source]
  [targetFintype : Fintype target]
  operator : FinitePiLpField source (SUNLieCoord Nc) →L[ℝ]
    FinitePiLpField target (SUNLieCoord Nc)
  dist : target → source → ℕ

/-- Fixed-rate exponential localization of a packaged rectangular kernel. -/
def CMP99Eq395TypedKernelData.ExponentialKernelBound
    (D : CMP99Eq395TypedKernelData Nc) (A rate : ℝ) : Prop := by
  letI := D.sourceFintype
  letI := D.sourceDecidableEq
  letI := D.targetFintype
  exact FinitePiLpTypedExponentialKernelBound D.operator D.dist A rate

noncomputable def cmp99Eq395GeneratedGreenWeightedAdjointAmplitude
    (M depth : ℕ) (spacing epsilon : ℝ) : ℝ :=
  let theta := cmp99SourceGeneratedCombesThomasRate
    4 M depth spacing epsilon
  let S := cmp99OmegaSiteExpSumBound (theta / 4)
  let R := M ^ (depth + 1) - 1
  let AW := cmp99SourceGeneratedWeightedAdjointNormBound M depth *
    Real.exp (theta * (R : ℝ))
  let AG := 2 / cmp99SourceGeneratedCoercivity
    4 M (depth + 1) spacing epsilon
  AG * AW * S

/-- The literal mixed-scale right factor `G W`, with its dependent source
and target coordinate types inferred once and kept opaque thereafter. -/
noncomputable def cmp99Eq395GeneratedGreenWeightedAdjoint
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
  let regions := cmp99SourceIteratedLiftActiveRegionChain
    (M := M) Omega (depth + 1)
  let W := regions.physicalWeightedAdjoint (show 2 ≤ 4 by norm_num) hM
    (matrixSUNAdjointModel Nc) spacing epsilon background
    budget.toRadiusChain fineSmall
  let G := cmp99SourceGeneratedPhysicalGreen (show 2 ≤ 4 by norm_num) hM
    Omega depth hspacing background budget fineSmall hsmall
  exact G.comp W

/-- Rectangular distance from a terminal source coordinate to a fine target
site.  Its dependent endpoint types are inferred once, alongside the
physical `G W` operator. -/
def cmp99Eq395GeneratedGreenWeightedAdjointDist
    (Omega : ActiveGaugeRegion 4 (2 * Q)) (depth : ℕ) :=
  let regions := cmp99SourceIteratedLiftActiveRegionChain
    (M := M) Omega (depth + 1)
  fun (target : ActiveGaugeRegion.Site
      (cmp99IteratedLiftActiveRegion (M := M) Omega (depth + 1)))
      (source : regions.terminalSite) =>
    finBoxDist target.1 (regions.terminalRepresentative source).1

/-- The operator and its physical terminal-to-fine distance packaged with
their endpoint types. -/
noncomputable def cmp99Eq395GeneratedGreenWeightedAdjointKernelData
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
    operator := cmp99Eq395GeneratedGreenWeightedAdjoint Omega hM depth
      hspacing background budget fineSmall hsmall
    dist := cmp99Eq395GeneratedGreenWeightedAdjointDist (M := M) Omega depth
  }

set_option maxRecDepth 4000
set_option maxHeartbeats 3000000 in
theorem cmp99Eq395GeneratedGreenWeightedAdjoint_exponentialKernelBound
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
    (cmp99Eq395GeneratedGreenWeightedAdjointKernelData Omega hM depth hspacing
      background budget fineSmall hsmall).ExponentialKernelBound
      (cmp99Eq395GeneratedGreenWeightedAdjointAmplitude
        M depth spacing epsilon)
      (3 * cmp99SourceGeneratedCombesThomasRate
        4 M depth spacing epsilon / 4) := by
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
  have hW :=
    cmp99Eq395GeneratedPhysicalWeightedAdjoint_exponentialKernelBound
      Omega hM depth hspacing htheta background budget fineSmall
  have hG := finitePiLpTypedExponentialKernelBound_of_square
    (cmp99SourceGeneratedPhysicalGreen_canonicalExponentialKernelBound
      (show 2 ≤ 4 by norm_num) hM Omega depth hspacing background budget
        fineSmall hsmall)
  have hsum : ∀ target : ActiveGaugeRegion.Site Omega',
      ∑ middle : ActiveGaugeRegion.Site Omega',
        Real.exp (-(sigma * (finBoxDist target.1 middle.1 : ℝ))) ≤ S := by
    intro target
    exact activeGaugeRegion_finBoxDist_exp_sum_le Omega' target hsigma
  have h := finitePiLpTypedExponentialKernelBound_comp
    (ι := regions.terminalSite)
    (κ := ActiveGaugeRegion.Site Omega')
    (ν := ActiveGaugeRegion.Site Omega')
    (g := SUNLieCoord Nc)
    (A := AG) (B := AW) (rate := theta) (sigma := sigma) (S := S)
    (fun target middle => finBoxDist target.1 middle.1)
    (fun middle source => finBoxDist middle.1
      (regions.terminalRepresentative source).1)
    (fun target source => finBoxDist target.1
      (regions.terminalRepresentative source).1)
    (fun target middle source => finBoxDist_triangle target.1 middle.1
      (regions.terminalRepresentative source).1)
    hsigma (by dsimp [sigma]; linarith) hS hsum G W
    (by simpa only [G, AG, theta] using hG)
    (by simpa only [W, AW, R, theta] using hW)
  change FinitePiLpTypedExponentialKernelBound (G.comp W)
    (cmp99Eq395GeneratedGreenWeightedAdjointDist (M := M) Omega depth)
    (cmp99Eq395GeneratedGreenWeightedAdjointAmplitude
      M depth spacing epsilon) (3 * theta / 4)
  have hamp : cmp99Eq395GeneratedGreenWeightedAdjointAmplitude
      M depth spacing epsilon = AG * AW * S := by
    rfl
  rw [hamp]
  convert h using 1 <;> ring

end
end YangMills.RG
