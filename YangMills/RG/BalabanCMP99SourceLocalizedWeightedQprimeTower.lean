import YangMills.RG.BalabanCMP99SourceLocalizedNextBackground
import YangMills.RG.BalabanCMP99SourceRetainedExactReadCarrier
import YangMills.RG.BalabanCMP99SourceWeightedRegionalTower

/-!
PRE-VALIDATION: source is present in scratch only; no `.olean` has been
materialized and no compiler or axiom-oracle verdict exists for this module.

# Localized weighted Qprime tower

This is the recursive consumer of the exact retained read carrier.  The input
background is assumed small only on that finite carrier.  Every successor
constructs the selected/identity coarse background from f3b, derives its
global next-scale radius internally, restricts that certificate to the tail
carrier, and recurses.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {d M N Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero N] [NeZero Nc]

/-- The tail-Ubar part of the recursive carrier inherits any pointwise
positive-link estimate imposed on the complete current carrier. -/
omit [NeZero N] in
theorem boundOn_tailUbarReadBonds_of_boundOn_retainedFineReadBonds
    {N' depth : ℕ} [NeZero N']
    (Omega : ActiveGaugeRegion d (M * N')) (hOmega : Omega.BlockSaturated)
    (tail : CMP99SourceActiveRegionChain d M N'
      (cmp99ActiveCoarseRegion (M := M) (N' := N') Omega) depth)
    (background : PhysicalGaugeBackground d (M * N') Nc)
    (epsilon : ℝ)
    (hsmall : ∀ q ∈ (CMP99SourceActiveRegionChain.step Omega hOmega tail).
        retainedFineReadBonds (Nc := Nc),
      ‖(background (positiveEdgeOfPhysicalBond q) :
          Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon) :
    ∀ q ∈ cmp99SourceUbarFineReadBondsOfCoarseBonds (Nc := Nc)
        (tail.retainedFineReadBonds (Nc := Nc)),
      ‖(background (positiveEdgeOfPhysicalBond q) :
          Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon := by
  intro q hq
  exact hsmall q (by
    rw [CMP99SourceActiveRegionChain.retainedFineReadBonds_step]
    exact Finset.mem_union_right _ hq)

/-- Literal source tower generated from smallness on the exact recursive read
carrier only.  No complete-torus `fineSmall` premise occurs. -/
noncomputable def CMP99SourceActiveRegionChain.localizedWeightedQprimeTower
    {N depth : ℕ} {Omega : ActiveGaugeRegion d N}
    (regions : CMP99SourceActiveRegionChain d M N Omega depth)
    (hd : 2 ≤ d) (hM : 2 ≤ M) (rho : SUNAdjointModel Nc) :
    letI : NeZero N := regions.neZero
    (spacing epsilon : ℝ) →
    (background : PhysicalGaugeBackground d N Nc) →
    (chain : CMP99SourceUbarRadiusChain d M Nc depth epsilon) →
    (∀ q ∈ regions.retainedFineReadBonds (Nc := Nc),
      ‖(background (positiveEdgeOfPhysicalBond q) :
          Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon) →
    CMP99SourceWeightedRegionalTower (g := SUNLieCoord Nc) Omega spacing := by
  letI : NeZero N := regions.neZero
  intro spacing epsilon background chain localSmall
  induction regions generalizing spacing epsilon with
  | stop Omega =>
      exact CMP99SourceWeightedRegionalTower.stop
        (g := SUNLieCoord Nc) Omega spacing
  | @step N' depth _ Omega hOmega tail ih =>
      letI : NeZero (M * N') := inferInstance
      let tailBonds := tail.retainedFineReadBonds (Nc := Nc)
      have tailPullSmall : ∀ q ∈
          cmp99SourceUbarFineReadBondsOfCoarseBonds (Nc := Nc) tailBonds,
          ‖(background (positiveEdgeOfPhysicalBond q) :
              Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon :=
        boundOn_tailUbarReadBonds_of_boundOn_retainedFineReadBonds
          Omega hOmega tail background epsilon localSmall
      let nextBackground : PhysicalGaugeBackground d N' Nc :=
        cmp99SourceLocalizedNextBackground hd hM background epsilon
          chain.epsilon_nonneg chain.head_noWinding tailBonds tailPullSmall
      have nextSmall : ∀ e : ConcreteEdge d N',
          ‖(nextBackground e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤
            cmp99SourceUbarNextFineRadius d M epsilon := by
        intro e
        exact norm_cmp99SourceLocalizedNextBackground_sub_one_le
          hd hM background epsilon chain.epsilon_nonneg
          chain.head_noWinding chain.head_logSmall tailBonds tailPullSmall e
      exact CMP99SourceWeightedRegionalTower.step Omega hOmega spacing
        (cmp99SourceWeightedPhysicalTransport rho background)
        (ih ((M : ℝ) * spacing)
          (cmp99SourceUbarNextFineRadius d M epsilon)
          nextBackground chain.tail (by
            intro q hq
            exact nextSmall (positiveEdgeOfPhysicalBond q)))

/-- The localized tower has exactly the length of its typed region chain. -/
theorem CMP99SourceActiveRegionChain.localizedWeightedQprimeTower_depth
    {depth : ℕ} {Omega : ActiveGaugeRegion d N}
    (regions : CMP99SourceActiveRegionChain d M N Omega depth)
    (hd : 2 ≤ d) (hM : 2 ≤ M) (rho : SUNAdjointModel Nc) :
    letI : NeZero N := regions.neZero
    ∀ (spacing epsilon : ℝ)
      (background : PhysicalGaugeBackground d N Nc)
      (chain : CMP99SourceUbarRadiusChain d M Nc depth epsilon)
      (localSmall : ∀ q ∈ regions.retainedFineReadBonds (Nc := Nc),
        ‖(background (positiveEdgeOfPhysicalBond q) :
            Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon),
      (regions.localizedWeightedQprimeTower hd hM rho spacing epsilon
        background chain localSmall).depth = depth := by
  letI : NeZero N := regions.neZero
  induction regions with
  | stop Omega =>
      intro spacing epsilon background chain localSmall
      rfl
  | @step N' depth _ Omega hOmega tail ih =>
      intro spacing epsilon background chain localSmall
      letI : NeZero (M * N') := inferInstance
      let tailBonds := tail.retainedFineReadBonds (Nc := Nc)
      have tailPullSmall : ∀ q ∈
          cmp99SourceUbarFineReadBondsOfCoarseBonds (Nc := Nc) tailBonds,
          ‖(background (positiveEdgeOfPhysicalBond q) :
              Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon :=
        boundOn_tailUbarReadBonds_of_boundOn_retainedFineReadBonds
          Omega hOmega tail background epsilon localSmall
      let nextBackground : PhysicalGaugeBackground d N' Nc :=
        cmp99SourceLocalizedNextBackground hd hM background epsilon
          chain.epsilon_nonneg chain.head_noWinding tailBonds tailPullSmall
      have nextSmall : ∀ e : ConcreteEdge d N',
          ‖(nextBackground e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤
            cmp99SourceUbarNextFineRadius d M epsilon := by
        intro e
        exact norm_cmp99SourceLocalizedNextBackground_sub_one_le
          hd hM background epsilon chain.epsilon_nonneg
          chain.head_noWinding chain.head_logSmall tailBonds tailPullSmall e
      change (tail.localizedWeightedQprimeTower hd hM rho
          ((M : ℝ) * spacing) (cmp99SourceUbarNextFineRadius d M epsilon)
          nextBackground chain.tail (fun q _ =>
            nextSmall (positiveEdgeOfPhysicalBond q))).depth + 1 = depth + 1
      rw [ih]

end

end YangMills.RG
