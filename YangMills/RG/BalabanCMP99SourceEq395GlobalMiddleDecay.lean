/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceEq395GlobalMiddleNorm
import YangMills.RG.BalabanCMP99SourceEq395GreenSquaredWeightedAdjointDecay

/-!
# Fixed-rate decay of the global middle in CMP99 equation (3.95)

The global middle is exposed in the literal terminal coordinates of the
generated averaging tower.  The exact identity between `Q'` and the adjoint
of the physical weighted synthesis then reduces its decay to two generated
Green kernels and two finite-range averaging kernels.  All intermediate row
sums are bounded on the lifted active region, so the result has no ambient
volume factor.
-/

namespace YangMills.RG
open YangMills Matrix
open scoped Matrix.Norms.L2Operator RealInnerProductSpace
noncomputable section

variable {M Nc Q : ℕ} [NeZero M] [NeZero Nc] [NeZero Q]

/-- The literal scale-normalization multiplying the adjoint synthesis in
the four-dimensional generated `Q'`. -/
noncomputable def cmp99Eq395GeneratedQprimeScale
    (M depth : ℕ) (spacing : ℝ) : ℝ :=
  spacing ^ 4 / (((M : ℝ) ^ (depth + 1) * spacing) ^ 4)

/-- Explicit volume-independent amplitude of the coordinate-exposed global
middle at one quarter of the generated Combes--Thomas rate. -/
noncomputable def cmp99Eq395GeneratedMiddleDecayAmplitude
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
  |cmp99Eq395GeneratedQprimeScale M depth spacing| * AW *
    (AG * (AG * AW * S) * S) * S

/-- The coordinate-exposed realization of the generated global middle.
Unlike the bundled tower definition, both endpoint types are literal finite
`PiLp` fields, so its kernel can be stated without an external equivalence. -/
noncomputable def cmp99Eq395GeneratedPhysicalMiddle
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
  exact (cmp99Eq395GeneratedQprimeScale M depth spacing • W.adjoint).comp
    (G.comp (G.comp W))

def cmp99Eq395GeneratedMiddleDist
    (Omega : ActiveGaugeRegion 4 (2 * Q)) (depth : ℕ) :=
  let regions := cmp99SourceIteratedLiftActiveRegionChain
    (M := M) Omega (depth + 1)
  fun (target source : regions.terminalSite) => finBoxDist
    (regions.terminalRepresentative target).1
    (regions.terminalRepresentative source).1

noncomputable def cmp99Eq395GeneratedPhysicalMiddleKernelData
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
  exact {
    source := regions.terminalSite
    target := regions.terminalSite
    operator := cmp99Eq395GeneratedPhysicalMiddle Omega hM depth hspacing
      background budget fineSmall hsmall
    dist := cmp99Eq395GeneratedMiddleDist (M := M) Omega depth
  }

set_option maxRecDepth 4000
set_option maxHeartbeats 8000000 in
/-- The coordinate-exposed global middle has fixed-rate exponential decay,
uniformly over every active region and hence over the ambient volume. -/
theorem cmp99Eq395GeneratedPhysicalMiddle_exponentialKernelBound
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
    (cmp99Eq395GeneratedPhysicalMiddleKernelData Omega hM depth hspacing
      background budget fineSmall hsmall).ExponentialKernelBound
      (cmp99Eq395GeneratedMiddleDecayAmplitude M depth spacing epsilon)
      (cmp99SourceGeneratedCombesThomasRate
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
  let beta := cmp99SourceGeneratedWeightedAdjointNormBound M depth
  let AW := beta * Real.exp (theta * (R : ℝ))
  let AG := 2 / cmp99SourceGeneratedCoercivity
    4 M (depth + 1) spacing epsilon
  let qscale := cmp99Eq395GeneratedQprimeScale M depth spacing
  have htheta : 0 < theta :=
    cmp99SourceGeneratedCombesThomasRate_pos
      4 M depth hspacing hsmall
  have hsigma : 0 < sigma := by dsimp [sigma]; positivity
  have hS : 0 ≤ S := by
    dsimp [S, cmp99OmegaSiteExpSumBound]
    exact tsum_nonneg fun _ => mul_nonneg (Nat.cast_nonneg _)
      (Real.exp_pos _).le
  have hW : FinitePiLpTypedExponentialKernelBound W
      (fun target source => finBoxDist target.1
      (regions.terminalRepresentative source).1) AW theta := by
    have h := cmp99Eq395GeneratedPhysicalWeightedAdjoint_exponentialKernelBound
      Omega hM depth hspacing htheta background budget fineSmall
    change FinitePiLpTypedExponentialKernelBound W
      (fun target source => finBoxDist target.1
        (regions.terminalRepresentative source).1)
      (cmp99SourceGeneratedWeightedAdjointNormBound M depth *
        Real.exp (theta * ((M ^ (depth + 1) - 1 : ℕ) : ℝ))) theta at h
    simpa only [AW, beta, R] using h
  have hWadj0 : FinitePiLpTypedExponentialKernelBound W.adjoint
      (fun target source => finBoxDist source.1
        (regions.terminalRepresentative target).1) AW theta :=
    finitePiLpTypedExponentialKernelBound_adjoint _ W hW
  have hWadj : FinitePiLpTypedExponentialKernelBound W.adjoint
      (fun target source => finBoxDist source.1
        (regions.terminalRepresentative target).1) AW (theta / 2) :=
    finitePiLpTypedExponentialKernelBound_mono_rate
      (by positivity) (by linarith) hWadj0
  have hQ : FinitePiLpTypedExponentialKernelBound (qscale • W.adjoint)
      (fun target source => finBoxDist source.1
        (regions.terminalRepresentative target).1)
      (|qscale| * AW) (theta / 2) :=
    finitePiLpTypedExponentialKernelBound_smul qscale hWadj
  have hGGW : FinitePiLpTypedExponentialKernelBound (G.comp (G.comp W))
      (fun target source => finBoxDist target.1
        (regions.terminalRepresentative source).1)
      (AG * (AG * AW * S) * S) (theta / 2) := by
    have h :=
      cmp99Eq395GeneratedGreenSquaredWeightedAdjoint_exponentialKernelBound
        Omega hM depth hspacing background budget fineSmall hsmall
    change FinitePiLpTypedExponentialKernelBound (G.comp (G.comp W))
      (fun target source => finBoxDist target.1
        (regions.terminalRepresentative source).1)
      (cmp99Eq395GeneratedGreenSquaredWeightedAdjointAmplitude
        M depth spacing epsilon) (theta / 2) at h
    have hamp : cmp99Eq395GeneratedGreenSquaredWeightedAdjointAmplitude
        M depth spacing epsilon = AG * (AG * AW * S) * S := rfl
    simpa only [hamp] using h
  have hsumQ : ∀ target : regions.terminalSite,
      ∑ middle : ActiveGaugeRegion.Site Omega',
        Real.exp (-(sigma * (finBoxDist middle.1
          (regions.terminalRepresentative target).1 : ℝ))) ≤ S := by
    intro target
    simpa [finBoxDist_comm] using
      activeGaugeRegion_finBoxDist_exp_sum_le Omega'
        (regions.terminalRepresentative target) hsigma
  have hFinal := finitePiLpTypedExponentialKernelBound_comp
    (ι := regions.terminalSite)
    (κ := ActiveGaugeRegion.Site Omega')
    (ν := regions.terminalSite)
    (g := SUNLieCoord Nc)
    (A := |qscale| * AW) (B := AG * (AG * AW * S) * S)
    (rate := theta / 2) (sigma := sigma) (S := S)
    (fun target middle => finBoxDist middle.1
      (regions.terminalRepresentative target).1)
    (fun middle source => finBoxDist middle.1
      (regions.terminalRepresentative source).1)
    (fun target source => finBoxDist
      (regions.terminalRepresentative target).1
      (regions.terminalRepresentative source).1)
    (fun target middle source => by
      simpa [finBoxDist_comm] using finBoxDist_triangle
        (regions.terminalRepresentative target).1 middle.1
        (regions.terminalRepresentative source).1)
    hsigma (by dsimp [sigma]; linarith) hS hsumQ
    (qscale • W.adjoint) (G.comp (G.comp W)) hQ hGGW
  change FinitePiLpTypedExponentialKernelBound
    ((qscale • W.adjoint).comp (G.comp (G.comp W)))
    (cmp99Eq395GeneratedMiddleDist (M := M) Omega depth)
    (cmp99Eq395GeneratedMiddleDecayAmplitude M depth spacing epsilon)
    (theta / 4)
  have hamp : cmp99Eq395GeneratedMiddleDecayAmplitude M depth spacing epsilon =
      (|qscale| * AW) * (AG * (AG * AW * S) * S) * S := rfl
  rw [hamp]
  convert hFinal using 1 <;> ring

end
end YangMills.RG
