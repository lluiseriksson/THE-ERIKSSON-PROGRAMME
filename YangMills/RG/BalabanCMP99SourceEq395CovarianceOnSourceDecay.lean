/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceEq395AmbientMiddleDecay
import YangMills.RG.BalabanCMP99SourceEq395LocalInverse
import YangMills.RG.FinitePiLpExponentialInverseDecay

/-!
# Fixed-rate decay of the generated covariance on its source region

The canonical terminal covariance is transported directly to the original
physical source carrier.  Its middle is the already reindexed generated
operator, so coercivity, the exact inverse identity, and exponential decay
can be combined without exposing a dependent Omega geometry.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator RealInnerProductSpace

noncomputable section

variable {M Nc Q : ℕ} [NeZero M] [NeZero Nc] [NeZero Q]

theorem isCoerciveCLM_cmp99SourceTerminalCLMTransport
    {E E' : CMP99SourceWeightedTowerHilbertSpace}
    (hE : E = E') (C : E.carrier →L[ℝ] E.carrier) {c : ℝ}
    (hC : IsCoerciveCLM C c) :
    IsCoerciveCLM (cmp99SourceTerminalCLMTransport hE hE C) c := by
  subst E'
  exact hC

/-- The literal generated covariance transported to the original physical
source-region coordinates. -/
noncomputable def cmp99Eq395GeneratedPhysicalCovarianceOnSource
    (Omega : ActiveGaugeRegion 4 (2 * Q))
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
    ActiveGaugeZeroCochain Omega (SUNLieCoord Nc) →L[ℝ]
      ActiveGaugeZeroCochain Omega (SUNLieCoord Nc) := by
  let C := cmp99SourceGeneratedPhysicalCoarseCovariance
    (show 2 ≤ 4 by norm_num) hM Omega depth hspacing background budget
    fineSmall hsmall
  have hs := cmp99SourceIteratedLift_weightedQprimeTower_terminalSpace_eq
    (show 2 ≤ 4 by norm_num) hM (matrixSUNAdjointModel Nc)
    Omega (depth + 1) spacing epsilon background budget.toRadiusChain fineSmall
  exact cmp99SourceTerminalCLMTransport hs hs C

/-- Direct bundle transport of the generated middle agrees with the explicit
physical source reindexing. -/
theorem cmp99Eq395GeneratedPhysicalMiddleDirect_eq_onSource
    (Omega : ActiveGaugeRegion 4 (2 * Q))
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
    let Middle := cmp99SourceGeneratedPhysicalCoarseCovarianceMiddle
      (show 2 ≤ 4 by norm_num) hM Omega depth hspacing background budget
      fineSmall hsmall
    let hs := cmp99SourceIteratedLift_weightedQprimeTower_terminalSpace_eq
      (show 2 ≤ 4 by norm_num) hM (matrixSUNAdjointModel Nc)
      Omega (depth + 1) spacing epsilon background budget.toRadiusChain fineSmall
    cmp99SourceTerminalCLMTransport hs hs Middle =
      cmp99Eq395GeneratedPhysicalMiddleOnSource Omega hM depth hspacing
        background budget fineSmall hsmall := by
  dsimp only
  let regions := cmp99SourceIteratedLiftActiveRegionChain
    (M := M) Omega (depth + 1)
  let T := regions.weightedQprimeTower (show 2 ≤ 4 by norm_num) hM
    (matrixSUNAdjointModel Nc) spacing epsilon background
    budget.toRadiusChain fineSmall
  let Middle := cmp99SourceGeneratedPhysicalCoarseCovarianceMiddle
    (show 2 ≤ 4 by norm_num) hM Omega depth hspacing background budget
    fineSmall hsmall
  let hT := regions.weightedQprimeTower_terminalSpace_eq
    (show 2 ≤ 4 by norm_num) hM (matrixSUNAdjointModel Nc)
    spacing epsilon background budget.toRadiusChain fineSmall
  let hCoord := regions.terminalHilbertSpace_eq_coordinate (Nc := Nc)
  let hPhys := cmp99SourceIteratedLiftActiveRegionChain_terminalHilbertSpace_eq
    (Nc := Nc) (M := M) Omega (depth + 1)
  have hgenerated :=
    cmp99SourceGeneratedPhysicalCoarseCovarianceMiddle_transport_eq
      Omega hM depth hspacing background budget fineSmall hsmall
  have hsource := cmp99Eq395GeneratedPhysicalMiddleOnSource_eq_transport
    Omega hM depth hspacing background budget fineSmall hsmall
  have htrans := cmp99SourceTerminalCLMTransport_trans
    (hT.trans hCoord) (hT.trans hCoord)
    (hCoord.symm.trans hPhys) (hCoord.symm.trans hPhys) Middle
  rw [hgenerated] at htrans
  rw [hsource, htrans]

/-- Coercivity of the reindexed generated middle on the source carrier. -/
theorem isCoerciveCLM_cmp99Eq395GeneratedPhysicalMiddleOnSource
    (Omega : ActiveGaugeRegion 4 (2 * Q))
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
    IsCoerciveCLM
      (cmp99Eq395GeneratedPhysicalMiddleOnSource Omega hM depth hspacing
        background budget fineSmall hsmall)
      ((cmp99SourceGeneratedPhysicalPrecisionUpperBound 4 M (depth + 1)
        spacing epsilon) ^ 2)⁻¹ := by
  let Middle := cmp99SourceGeneratedPhysicalCoarseCovarianceMiddle
    (show 2 ≤ 4 by norm_num) hM Omega depth hspacing background budget
    fineSmall hsmall
  have hs := cmp99SourceIteratedLift_weightedQprimeTower_terminalSpace_eq
    (show 2 ≤ 4 by norm_num) hM (matrixSUNAdjointModel Nc)
    Omega (depth + 1) spacing epsilon background budget.toRadiusChain fineSmall
  rw [← cmp99Eq395GeneratedPhysicalMiddleDirect_eq_onSource
    Omega hM depth hspacing background budget fineSmall hsmall]
  exact isCoerciveCLM_cmp99SourceTerminalCLMTransport hs Middle
    (isCoerciveCLM_cmp99SourceGeneratedPhysicalCoarseCovarianceMiddle
      (show 2 ≤ 4 by norm_num) hM Omega depth hspacing background budget
        fineSmall hsmall)

/-- Exact inverse identity on the original physical source carrier. -/
theorem cmp99Eq395GeneratedPhysicalMiddleOnSource_comp_covariance
    (Omega : ActiveGaugeRegion 4 (2 * Q))
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
    (cmp99Eq395GeneratedPhysicalMiddleOnSource Omega hM depth hspacing
      background budget fineSmall hsmall).comp
      (cmp99Eq395GeneratedPhysicalCovarianceOnSource Omega hM depth hspacing
        background budget fineSmall hsmall) =
      ContinuousLinearMap.id ℝ _ := by
  let Middle := cmp99SourceGeneratedPhysicalCoarseCovarianceMiddle
    (show 2 ≤ 4 by norm_num) hM Omega depth hspacing background budget
    fineSmall hsmall
  let C := cmp99SourceGeneratedPhysicalCoarseCovariance
    (show 2 ≤ 4 by norm_num) hM Omega depth hspacing background budget
    fineSmall hsmall
  have hs := cmp99SourceIteratedLift_weightedQprimeTower_terminalSpace_eq
    (show 2 ≤ 4 by norm_num) hM (matrixSUNAdjointModel Nc)
    Omega (depth + 1) spacing epsilon background budget.toRadiusChain fineSmall
  rw [← cmp99Eq395GeneratedPhysicalMiddleDirect_eq_onSource
    Omega hM depth hspacing background budget fineSmall hsmall]
  have hinverse : Middle.comp C = ContinuousLinearMap.id ℝ _ :=
    cmp99SourceGeneratedPhysicalCoarseCovariance_middle_comp
      (show 2 ≤ 4 by norm_num) hM Omega depth hspacing background budget
        fineSmall hsmall
  change (cmp99SourceTerminalCLMTransport hs hs Middle).comp
      (cmp99SourceTerminalCLMTransport hs hs C) = _
  rw [cmp99SourceTerminalCLMTransport_comp, hinverse]
  exact cmp99SourceTerminalCLMTransport_id hs

/-- Canonical covariance decay rate for the generated coarse inverse used in
equation (3.95). -/
noncomputable def cmp99Eq395GeneratedCovarianceDecayRate
    (M depth : ℕ) (spacing epsilon : ℝ) : ℝ :=
  let decay :=
    cmp99SourceGeneratedCombesThomasRate 4 M depth spacing epsilon / 4
  let amplitude :=
    cmp99Eq395GeneratedMiddleDecayAmplitude M depth spacing epsilon
  let rowSum := cmp99OmegaSiteExpSumBound (decay / 4)
  let coercivity := ((cmp99SourceGeneratedPhysicalPrecisionUpperBound
    4 M (depth + 1) spacing epsilon) ^ 2)⁻¹
  finitePiLpExponentialInverseDecayRate
    amplitude decay rowSum coercivity

set_option maxRecDepth 4000 in
set_option maxHeartbeats 8000000 in
/-- Volume-independent exponential decay of the literal generated covariance
on an arbitrary physical source region. -/
theorem cmp99Eq395GeneratedPhysicalCovarianceOnSource_exponentialKernelBound
    (Omega : ActiveGaugeRegion 4 (2 * Q))
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
    let C := cmp99Eq395GeneratedPhysicalCovarianceOnSource Omega hM depth
      hspacing background budget fineSmall hsmall
    let decay :=
      cmp99SourceGeneratedCombesThomasRate 4 M depth spacing epsilon / 4
    let amplitude :=
      cmp99Eq395GeneratedMiddleDecayAmplitude M depth spacing epsilon
    let rowSum := cmp99OmegaSiteExpSumBound (decay / 4)
    let coercivity := ((cmp99SourceGeneratedPhysicalPrecisionUpperBound
      4 M (depth + 1) spacing epsilon) ^ 2)⁻¹
    FinitePiLpExponentialKernelBound C
      (fun target source => finBoxDist target.1 source.1)
      (2 / coercivity)
      (finitePiLpExponentialInverseDecayRate
        amplitude decay rowSum coercivity) := by
  dsimp only
  let K := cmp99Eq395GeneratedPhysicalMiddleOnSource Omega hM depth hspacing
    background budget fineSmall hsmall
  let C := cmp99Eq395GeneratedPhysicalCovarianceOnSource Omega hM depth
    hspacing background budget fineSmall hsmall
  let decay :=
    cmp99SourceGeneratedCombesThomasRate 4 M depth spacing epsilon / 4
  let amplitude :=
    cmp99Eq395GeneratedMiddleDecayAmplitude M depth spacing epsilon
  let rowSum := cmp99OmegaSiteExpSumBound (decay / 4)
  let coercivity := ((cmp99SourceGeneratedPhysicalPrecisionUpperBound
    4 M (depth + 1) spacing epsilon) ^ 2)⁻¹
  have hdecay : 0 < decay := by
    dsimp [decay]
    positivity [cmp99SourceGeneratedCombesThomasRate_pos
      4 M depth hspacing hsmall]
  have hcoercivity : 0 < coercivity := by
    dsimp [coercivity]
    positivity [cmp99SourceGeneratedPhysicalPrecisionUpperBound_pos
      4 M (depth + 1) (epsilon := epsilon) hspacing]
  have hrowSum : 0 ≤ rowSum := by
    dsimp [rowSum, cmp99OmegaSiteExpSumBound]
    exact tsum_nonneg fun _ => mul_nonneg (Nat.cast_nonneg _)
      (Real.exp_pos _).le
  have hK : FinitePiLpExponentialKernelBound K
      (fun target source => finBoxDist target.1 source.1)
      amplitude decay :=
    cmp99Eq395GeneratedPhysicalMiddleOnSource_exponentialKernelBound
      Omega hM depth hspacing background budget fineSmall hsmall
  have hexpSum : ∀ target : ActiveGaugeRegion.Site Omega,
      ∑ source : ActiveGaugeRegion.Site Omega, Real.exp (-((decay / 4) *
        (finBoxDist target.1 source.1 : ℝ))) ≤ rowSum := by
    intro target
    exact activeGaugeRegion_finBoxDist_exp_sum_le Omega target (by positivity)
  refine finitePiLpExponentialKernelBound_inverse_canonical
    (ι := ActiveGaugeRegion.Site Omega) (g := SUNLieCoord Nc)
    (amplitude := amplitude) (decay := decay) (rowSum := rowSum)
    (coercivity := coercivity)
    (fun target source => finBoxDist target.1 source.1)
    (fun p q => by simp [finBoxDist_comm])
    (fun p q r => finBoxDist_triangle p.1 q.1 r.1)
    (fun p => finBoxDist_self p.1)
    K C hdecay hcoercivity hrowSum hK ?_ ?_ hexpSum
  · exact isCoerciveCLM_cmp99Eq395GeneratedPhysicalMiddleOnSource
      Omega hM depth hspacing background budget fineSmall hsmall
  · exact cmp99Eq395GeneratedPhysicalMiddleOnSource_comp_covariance
      Omega hM depth hspacing background budget fineSmall hsmall

end

end YangMills.RG
