import YangMills.RG.BalabanCMP99SourcePhysicalRealSliceTower
import YangMills.RG.BalabanCMP99Eq359ComplexRegionalTowerPair

/-!
# A common-target pair of source-generated physical real-slice towers

The terminal complex Hilbert bundle of the source recursion depends only on
the typed active-region chain, not on the background or radius proofs.  This
file records that fact and uses it to place two independently generated
physical real-slice towers on one target.  The target equality is proved
internally; it is never accepted from the caller.
-/

namespace YangMills.RG

noncomputable section

open YangMills Matrix
open scoped Matrix.Norms.L2Operator

variable {d M N Nc depth : ℕ}
variable [NeZero d] [NeZero M] [NeZero N] [NeZero Nc]

/-- Canonical complex terminal Hilbert bundle of one typed source chain. -/
noncomputable def CMP99SourceActiveRegionChain.complexTerminalHilbertSpace
    {Omega : ActiveGaugeRegion d N}
    (regions : CMP99SourceActiveRegionChain d M N Omega depth) :
    CMP99ComplexTowerHilbertSpace := by
  induction regions with
  | stop Omega =>
      exact {
        carrier := ActiveGaugeZeroCochain Omega (SUNLieComplexCoord Nc) }
  | step Omega hOmega tail ih => exact ih

omit [NeZero N] in
/-- The source-generated analytic real-slice tower ends on the canonical
complex terminal bundle determined only by `regions`. -/
theorem CMP99SourceActiveRegionChain.physicalRealSliceComplexTower_terminalSpace_eq
    {Omega : ActiveGaugeRegion d N}
    (regions : CMP99SourceActiveRegionChain d M N Omega depth)
    (hd : 2 ≤ d) (hM : 2 ≤ M) :
    letI : NeZero N := regions.neZero
    ∀ (spacing epsilon : ℝ) (background : PhysicalGaugeBackground d N Nc)
      (chain : CMP99SourceUbarRadiusChain d M Nc depth epsilon)
      (fineSmall : ∀ e : ConcreteEdge d N,
        ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon),
      (regions.physicalRealSliceComplexTower hd hM spacing epsilon
        background chain fineSmall).toComplexTower.TerminalSpace =
        regions.complexTerminalHilbertSpace (Nc := Nc) := by
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
      exact ih ((M : ℝ) * spacing)
        (cmp99SourceUbarNextFineRadius d M epsilon)
        Scale.toSourceScale.data.nextBackground chain.tail nextSmall

/-- Transport the forward operator of a second analytic tower to the
internally proved terminal bundle of the first. -/
noncomputable def cmp99Eq359ComplexTowerQprimeTransport
    {Omega : ActiveGaugeRegion d N} {spacing : ℝ}
    (T0 T1 : CMP99ComplexRegionalTower (Nc := Nc) Omega spacing)
    (h : T1.TerminalSpace = T0.TerminalSpace) :
    ActiveGaugeZeroCochain Omega (SUNLieComplexCoord Nc) →L[ℂ]
      T0.TerminalSpace.carrier := by
  exact h ▸ T1.Qprime

/-- Transport the independently generated printed-starred operator in the
opposite direction along the same internally proved bundle equality. -/
noncomputable def cmp99Eq359ComplexTowerStarredTransport
    {Omega : ActiveGaugeRegion d N} {spacing : ℝ}
    (T0 T1 : CMP99ComplexRegionalTower (Nc := Nc) Omega spacing)
    (h : T1.TerminalSpace = T0.TerminalSpace) :
    T0.TerminalSpace.carrier →L[ℂ]
      ActiveGaugeZeroCochain Omega (SUNLieComplexCoord Nc) := by
  exact h ▸ T1.starred

/-- Pair two source-generated compact-real-slice towers on the canonical
target determined by the common region chain.  Radius chains and backgrounds
may differ, but no terminal equality or operator is input. -/
noncomputable def CMP99SourceActiveRegionChain.physicalRealSliceComplexTowerPair
    {Omega : ActiveGaugeRegion d N}
    (regions : CMP99SourceActiveRegionChain d M N Omega depth)
    (hd : 2 ≤ d) (hM : 2 ≤ M) (spacing : ℝ)
    (epsilon0 epsilon1 : ℝ)
    (background0 background1 : PhysicalGaugeBackground d N Nc)
    (chain0 : CMP99SourceUbarRadiusChain d M Nc depth epsilon0)
    (chain1 : CMP99SourceUbarRadiusChain d M Nc depth epsilon1)
    (fineSmall0 : ∀ e : ConcreteEdge d N,
      ‖(background0 e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon0)
    (fineSmall1 : ∀ e : ConcreteEdge d N,
      ‖(background1 e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon1) :
    letI : NeZero N := regions.neZero
    CMP99Eq359ComplexRegionalTowerPair (Nc := Nc) Omega spacing := by
  letI : NeZero N := regions.neZero
  let T0 := (regions.physicalRealSliceComplexTower hd hM spacing epsilon0
    background0 chain0 fineSmall0).toComplexTower
  let T1 := (regions.physicalRealSliceComplexTower hd hM spacing epsilon1
    background1 chain1 fineSmall1).toComplexTower
  have h0 : T0.TerminalSpace =
      regions.complexTerminalHilbertSpace (Nc := Nc) :=
    regions.physicalRealSliceComplexTower_terminalSpace_eq hd hM spacing
      epsilon0 background0 chain0 fineSmall0
  have h1 : T1.TerminalSpace =
      regions.complexTerminalHilbertSpace (Nc := Nc) :=
    regions.physicalRealSliceComplexTower_terminalSpace_eq hd hM spacing
      epsilon1 background1 chain1 fineSmall1
  have h10 : T1.TerminalSpace = T0.TerminalSpace := h1.trans h0.symm
  exact {
    depth := T0.depth
    TerminalSpace := T0.TerminalSpace
    terminalSpacing := T0.terminalSpacing
    Q0 := T0.Qprime
    Q1 := cmp99Eq359ComplexTowerQprimeTransport T0 T1 h10
    starred0 := T0.starred
    starred1 := cmp99Eq359ComplexTowerStarredTransport T0 T1 h10 }

end

end YangMills.RG
