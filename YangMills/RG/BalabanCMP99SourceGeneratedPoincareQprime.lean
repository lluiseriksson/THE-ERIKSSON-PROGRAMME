/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceGeneratedPoincareAbsorption
import YangMills.RG.BalabanCMP99SourceWeightedRegionalTower

/-!
# The generated Poincare tower as the literal `Q'_j`

The typed source region chain already makes every coarse domain definitionally
equal to the next domain.  Recursing directly on that chain therefore builds
the printed weighted regional tower without casts between unrelated operator
spaces.  Its terminal field is exactly the field used in the multiscale
Poincare argument.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {d M N Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero N] [NeZero Nc]

/-- The literal weighted `Q'_j` tower generated on one typed source region
chain.  Every background and average is produced by the physical `Ubar`
recursion. -/
noncomputable def CMP99SourceActiveRegionChain.weightedQprimeTower
    {N depth : ℕ} {Omega : ActiveGaugeRegion d N}
    (regions : CMP99SourceActiveRegionChain d M N Omega depth)
    (hd : 2 ≤ d) (hM : 2 ≤ M)
    (rho : SUNAdjointModel Nc) :
    letI : NeZero N := regions.neZero
    (spacing epsilon : ℝ) → (background : GaugeConfig d N (SUN Nc)) →
    (chain : CMP99SourceUbarRadiusChain d M Nc depth epsilon) →
    (fineSmall : ∀ e : ConcreteEdge d N,
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon) →
    CMP99SourceWeightedRegionalTower (g := SUNLieCoord Nc) Omega spacing := by
  letI : NeZero N := regions.neZero
  intro spacing epsilon background chain fineSmall
  induction regions generalizing spacing epsilon with
  | stop Omega =>
      exact CMP99SourceWeightedRegionalTower.stop
        (g := SUNLieCoord Nc) Omega spacing
  | @step N' depth _ Omega hOmega tail ih =>
      letI : NeZero (M * N') := inferInstance
      let Scale : CMP99SourceNormalizedRegionalScale Omega background :=
        CMP99SourceNormalizedRegionalScale.ofFineSmall hd hM Omega background
          hOmega epsilon chain.epsilon_nonneg chain.head_noWinding fineSmall
      have nextSmall : ∀ e : ConcreteEdge d N',
          ‖(Scale.toSourceScale.data.nextBackground e :
              Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤
            cmp99SourceUbarNextFineRadius d M epsilon := by
        intro e
        simpa [Scale, CMP99SourceNormalizedRegionalScale.ofFineSmall,
          CMP99SourceRegionalScale.ofFineSmall] using
          norm_cmp99SourceRegionalScaleDataOfFineSmall_nextBackground_sub_one_le
            hd hM Omega background (cmp99SourceBlockAverageWeight M d)
            epsilon chain.epsilon_nonneg chain.head_noWinding
            chain.head_logSmall fineSmall e
      exact CMP99SourceWeightedRegionalTower.step Omega hOmega spacing
        (cmp99SourceWeightedPhysicalTransport rho background)
        (ih ((M : ℝ) * spacing)
          (cmp99SourceUbarNextFineRadius d M epsilon)
          Scale.toSourceScale.data.nextBackground chain.tail nextSmall)

/-- The generated tower has exactly the length of the typed source chain. -/
theorem CMP99SourceActiveRegionChain.weightedQprimeTower_depth
    {depth : ℕ} {Omega : ActiveGaugeRegion d N}
    (regions : CMP99SourceActiveRegionChain d M N Omega depth)
    (hd : 2 ≤ d) (hM : 2 ≤ M) (rho : SUNAdjointModel Nc) :
    letI : NeZero N := regions.neZero
    ∀ (spacing epsilon : ℝ) (background : GaugeConfig d N (SUN Nc))
      (chain : CMP99SourceUbarRadiusChain d M Nc depth epsilon)
      (fineSmall : ∀ e : ConcreteEdge d N,
        ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon),
      (regions.weightedQprimeTower hd hM rho spacing epsilon background
        chain fineSmall).depth = depth := by
  letI : NeZero N := regions.neZero
  induction regions with
  | stop Omega =>
      intro spacing epsilon background chain fineSmall
      rfl
  | @step N' depth _ Omega hOmega tail ih =>
      intro spacing epsilon background chain fineSmall
      letI : NeZero (M * N') := inferInstance
      let Scale : CMP99SourceNormalizedRegionalScale Omega background :=
        CMP99SourceNormalizedRegionalScale.ofFineSmall hd hM Omega background
          hOmega epsilon chain.epsilon_nonneg chain.head_noWinding fineSmall
      have nextSmall : ∀ e : ConcreteEdge d N',
          ‖(Scale.toSourceScale.data.nextBackground e :
              Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤
            cmp99SourceUbarNextFineRadius d M epsilon := by
        intro e
        simpa [Scale, CMP99SourceNormalizedRegionalScale.ofFineSmall,
          CMP99SourceRegionalScale.ofFineSmall] using
          norm_cmp99SourceRegionalScaleDataOfFineSmall_nextBackground_sub_one_le
            hd hM Omega background (cmp99SourceBlockAverageWeight M d)
            epsilon chain.epsilon_nonneg chain.head_noWinding
            chain.head_logSmall fineSmall e
      change (tail.weightedQprimeTower hd hM rho ((M : ℝ) * spacing)
          (cmp99SourceUbarNextFineRadius d M epsilon)
          Scale.toSourceScale.data.nextBackground chain.tail nextSmall).depth + 1 =
        depth + 1
      rw [ih]

/-- The Poincare terminal field is literally the image under the generated
`Q'_j`, not a second recursively specified field. -/
theorem CMP99SourceActiveRegionChain.terminalFieldNormSq_eq_weightedQprimeTower
    {depth : ℕ} {Omega : ActiveGaugeRegion d N}
    (regions : CMP99SourceActiveRegionChain d M N Omega depth)
    (hd : 2 ≤ d) (hM : 2 ≤ M) :
    letI : NeZero N := regions.neZero
    ∀ (spacing epsilon : ℝ) (background : GaugeConfig d N (SUN Nc))
      (chain : CMP99SourceUbarRadiusChain d M Nc depth epsilon)
      (fineSmall : ∀ e : ConcreteEdge d N,
        ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
      (phi : ActiveGaugeZeroCochain Omega (SUNLieCoord Nc)),
      regions.terminalFieldNormSq hd hM epsilon background chain fineSmall phi =
        ‖(regions.weightedQprimeTower hd hM (matrixSUNAdjointModel Nc)
          spacing epsilon background chain fineSmall).Qprime phi‖ ^ 2 := by
  letI : NeZero N := regions.neZero
  induction regions with
  | stop Omega =>
      intro spacing epsilon background chain fineSmall phi
      rfl
  | @step N' depth _ Omega hOmega tail ih =>
      intro spacing epsilon background chain fineSmall phi
      letI : NeZero (M * N') := inferInstance
      let Scale : CMP99SourceNormalizedRegionalScale Omega background :=
        CMP99SourceNormalizedRegionalScale.ofFineSmall hd hM Omega background
          hOmega epsilon chain.epsilon_nonneg chain.head_noWinding fineSmall
      have nextSmall : ∀ e : ConcreteEdge d N',
          ‖(Scale.toSourceScale.data.nextBackground e :
              Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤
            cmp99SourceUbarNextFineRadius d M epsilon := by
        intro e
        simpa [Scale, CMP99SourceNormalizedRegionalScale.ofFineSmall,
          CMP99SourceRegionalScale.ofFineSmall] using
          norm_cmp99SourceRegionalScaleDataOfFineSmall_nextBackground_sub_one_le
            hd hM Omega background (cmp99SourceBlockAverageWeight M d)
            epsilon chain.epsilon_nonneg chain.head_noWinding
            chain.head_logSmall fineSmall e
      let coarsePhi := cmp99SourceTransportedBlockAverageCLM Omega
        (cmp99SourceWeightedPhysicalTransport
          (matrixSUNAdjointModel Nc) background) phi
      have htail := ih ((M : ℝ) * spacing)
        (cmp99SourceUbarNextFineRadius d M epsilon)
        Scale.toSourceScale.data.nextBackground chain.tail nextSmall coarsePhi
      change tail.terminalFieldNormSq hd hM
          (cmp99SourceUbarNextFineRadius d M epsilon)
          Scale.toSourceScale.data.nextBackground chain.tail nextSmall coarsePhi =
        ‖(tail.weightedQprimeTower hd hM (matrixSUNAdjointModel Nc)
            ((M : ℝ) * spacing)
            (cmp99SourceUbarNextFineRadius d M epsilon)
            Scale.toSourceScale.data.nextBackground chain.tail nextSmall).Qprime
          coarsePhi‖ ^ 2
      exact htail

/-- Exact source-Hilbert coisometry of the generated `Q'_j`. -/
theorem CMP99SourceActiveRegionChain.weightedQprimeTower_comp_weightedAdjoint
    {depth : ℕ} {Omega : ActiveGaugeRegion d N}
    (regions : CMP99SourceActiveRegionChain d M N Omega depth)
    (hd : 2 ≤ d) (hM : 2 ≤ M) (rho : SUNAdjointModel Nc)
    (spacing epsilon : ℝ) (background : GaugeConfig d N (SUN Nc))
    (chain : CMP99SourceUbarRadiusChain d M Nc depth epsilon)
    (fineSmall : ∀ e : ConcreteEdge d N,
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon) :
    let T := regions.weightedQprimeTower hd hM rho spacing epsilon background
      chain fineSmall
    T.Qprime.comp T.weightedAdjoint =
      ContinuousLinearMap.id ℝ T.TerminalSpace.carrier := by
  dsimp only
  exact (regions.weightedQprimeTower hd hM rho spacing epsilon background
    chain fineSmall).Qprime_comp_weightedAdjoint

/-- Exact `sqrt C_j` law in the source spacing-weighted Hilbert convention
for the generated tower. -/
theorem CMP99SourceActiveRegionChain.weightedQprimeTower_weightedAdjoint_norm
    {depth : ℕ} {Omega : ActiveGaugeRegion d N}
    (regions : CMP99SourceActiveRegionChain d M N Omega depth)
    (hd : 2 ≤ d) (hM : 2 ≤ M) (rho : SUNAdjointModel Nc)
    (spacing epsilon : ℝ) (background : GaugeConfig d N (SUN Nc))
    (chain : CMP99SourceUbarRadiusChain d M Nc depth epsilon)
    (fineSmall : ∀ e : ConcreteEdge d N,
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (eta : (regions.weightedQprimeTower hd hM rho spacing epsilon background
      chain fineSmall).TerminalSpace.carrier) :
    let T := regions.weightedQprimeTower hd hM rho spacing epsilon background
      chain fineSmall
    cmp99SourceSpacingNorm d spacing (T.weightedAdjoint eta) =
      Real.sqrt (cmp99SourceTowerNormalization depth) *
        cmp99SourceSpacingNorm d T.terminalSpacing eta := by
  dsimp only
  have h := (regions.weightedQprimeTower hd hM rho spacing epsilon background
    chain fineSmall).weightedAdjoint_norm_eq_sqrt_Cj eta
  rw [regions.weightedQprimeTower_depth hd hM rho spacing epsilon background
    chain fineSmall] at h
  exact h

/-- Canonical absorbed Poincare estimate with the retained term written as
the literal source-generated `Q'_j`. -/
theorem cmp99SourceIteratedLift_norm_sq_le_absorbed_poincare_with_Qprime
    (hd : 2 ≤ d) (hM : 2 ≤ M) (Omega : ActiveGaugeRegion d N)
    (depth : ℕ) {spacing epsilon : ℝ} (hspacing : 0 < spacing)
    (background : GaugeConfig d
      (cmp99RegionalLatticeSize M N depth) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget d M Nc depth epsilon)
    (fineSmall : ∀ e : ConcreteEdge d
      (cmp99RegionalLatticeSize M N depth),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (phi : ActiveGaugeZeroCochain
      (cmp99IteratedLiftActiveRegion (M := M) Omega depth)
      (SUNLieCoord Nc))
    (hsmall : cmp99SourcePoincareErrorCoeff d M depth spacing epsilon < 1) :
    let regions := cmp99SourceIteratedLiftActiveRegionChain
      (M := M) Omega depth
    let chain := budget.toRadiusChain
    let T := regions.weightedQprimeTower hd hM (matrixSUNAdjointModel Nc)
      spacing epsilon background chain fineSmall
    ‖phi‖ ^ 2 ≤
      (cmp99SourcePoincareEnergyCoeff d M depth spacing epsilon *
            regions.scaledGradientEnergy hd hM spacing epsilon background chain
              fineSmall 0 phi +
          cmp99OneScaleBlockPoincareConstant d M ^ depth *
            ‖T.Qprime phi‖ ^ 2) /
        (1 - cmp99SourcePoincareErrorCoeff d M depth spacing epsilon) := by
  dsimp only
  have h := cmp99SourceIteratedLift_norm_sq_le_absorbed_poincare_of_closedBudget
    hd hM Omega depth hspacing background budget fineSmall phi hsmall
  dsimp only at h
  rw [(cmp99SourceIteratedLiftActiveRegionChain
      (M := M) Omega depth).terminalFieldNormSq_eq_weightedQprimeTower
        hd hM spacing epsilon background budget.toRadiusChain fineSmall phi] at h
  exact h

end

end YangMills.RG
