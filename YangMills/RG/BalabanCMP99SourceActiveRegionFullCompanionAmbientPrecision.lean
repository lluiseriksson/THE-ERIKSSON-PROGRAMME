import YangMills.RG.BalabanCMP99SourceActiveRegionFullCompanionPrecision
import YangMills.RG.BalabanCMP99SourceGeneratedPhysicalAmbientDictionary

/-!
PRE-VALIDATION: source present; `.olean` not yet materialized and the result
has not yet been verified by the compiler or axiom oracle.

# Ambient realization of the canonical full-companion precision

The full active carrier is explicitly equivalent to the ordinary ambient
`FinBox`.  Reindexing both legs through that equivalence produces the single
ambient precision consumed by the regional Dirichlet Green constructor.
Coercivity is preserved isometrically, and its Dirichlet compression is the
literal regional source precision already produced by the C6d chain.

The equivalence and both compression legs are constructed here; no equality
between independently supplied operators is accepted.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator RealInnerProductSpace

noncomputable section

variable {d M N Nc : ℕ} [NeZero d] [NeZero M] [NeZero N] [NeZero Nc]

/-- Coordinate equivalence from the literal full active region to the
ordinary ambient periodic box on the same carrier. -/
noncomputable def cmp99SourceFullActiveRegionSiteEquiv (d N : ℕ) :
    ActiveGaugeRegion.Site (cmp99SourceFullActiveRegion d N) ≃ FinBox d N where
  toFun x := x.1
  invFun x := ⟨x, Finset.mem_univ x⟩
  left_inv x := by
    apply Subtype.ext
    rfl
  right_inv _x := rfl

/-- Ambient reindexing of the internally constructed full-companion source
precision. -/
noncomputable def cmp99SourceActiveRegionFullCompanionAmbientPrecision
    {Omega : ActiveGaugeRegion d N} {depth : ℕ}
    (regions : CMP99SourceActiveRegionChain d M N Omega depth)
    (hd : 2 ≤ d) (hM : 2 ≤ M) (rho : SUNAdjointModel Nc)
    (spacing epsilon : ℝ) (background : GaugeConfig d N (SUN Nc))
    (chain : CMP99SourceUbarRadiusChain d M Nc depth epsilon)
    (fineSmall : ∀ e : ConcreteEdge d N,
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon) :
    GaugeZeroCochain d N (SUNLieCoord Nc) →L[ℝ]
      GaugeZeroCochain d N (SUNLieCoord Nc) :=
  finitePiLpTypedKernelReindex
    (cmp99SourceFullActiveRegionSiteEquiv d N)
    (cmp99SourceFullActiveRegionSiteEquiv d N)
    (cmp99SourceActiveRegionFullCompanionPrecision regions hd hM rho spacing
      epsilon background chain fineSmall)

/-- The ambient reindexing preserves the full-companion coercivity floor
exactly. -/
theorem isCoerciveCLM_cmp99SourceActiveRegionFullCompanionAmbientPrecision
    {Omega : ActiveGaugeRegion d N} {depth : ℕ}
    (regions : CMP99SourceActiveRegionChain d M N Omega depth)
    (hd : 2 ≤ d) (hM : 2 ≤ M) (hdepth : 0 < depth)
    (rho : SUNAdjointModel Nc) {spacing epsilon : ℝ}
    (hspacing : 0 < spacing)
    (background : GaugeConfig d N (SUN Nc))
    (chain : CMP99SourceUbarRadiusChain d M Nc depth epsilon)
    (fineSmall : ∀ e : ConcreteEdge d N,
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff d M depth spacing epsilon < 1) :
    let T := cmp99SourceActiveRegionFullCompanionTower regions hd hM rho
      spacing epsilon background chain fineSmall
    IsCoerciveCLM
      (cmp99SourceActiveRegionFullCompanionAmbientPrecision regions hd hM rho
        spacing epsilon background chain fineSmall)
      (cmp99SourceActiveRegionTerminalPhysicalCoercivity T M depth epsilon) := by
  exact isCoerciveCLM_finitePiLpTypedKernelReindex
    (cmp99SourceFullActiveRegionSiteEquiv d N)
    (cmp99SourceActiveRegionFullCompanionPrecision regions hd hM rho spacing
      epsilon background chain fineSmall)
    (isCoerciveCLM_cmp99SourceActiveRegionFullCompanionPrecision regions hd hM
      hdepth rho hspacing background chain fineSmall hsmall)

/-- Dirichlet compression after the explicit full-site reindexing is exactly
the regional source precision with its regional source-flow coefficient. -/
theorem cmp99RegionalDirichletPrecision_fullCompanionAmbient_eq
    {Omega : ActiveGaugeRegion d N} {depth : ℕ}
    (regions : CMP99SourceActiveRegionChain d M N Omega depth)
    (hd : 2 ≤ d) (hM : 2 ≤ M) (rho : SUNAdjointModel Nc)
    (spacing epsilon : ℝ) (background : GaugeConfig d N (SUN Nc))
    (chain : CMP99SourceUbarRadiusChain d M Nc depth epsilon)
    (fineSmall : ∀ e : ConcreteEdge d N,
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon) :
    let Tregional := regions.weightedQprimeTower hd hM rho spacing epsilon
      background chain fineSmall
    cmp99RegionalDirichletPrecision Omega
        (cmp99SourceActiveRegionFullCompanionAmbientPrecision regions hd hM rho
          spacing epsilon background chain fineSmall) =
      cmp99SourceGaugePrecision
        (cmp99ActiveRegionSourceCovariantLaplacian Omega rho background spacing)
        Tregional.Qprime
        (cmp99SourceActiveRegionTerminalPhysicalCountingCoefficient Tregional
          (cmp99SourceMassParameter 1 (M : ℝ) depth)) := by
  let R := cmp99NestedActiveRegionRestriction (g := SUNLieCoord Nc) Omega
    (cmp99SourceFullActiveRegion d N)
  let E := cmp99NestedActiveRegionExtension (g := SUNLieCoord Nc) Omega
    (cmp99SourceFullActiveRegion d N)
  let Kfull := cmp99SourceActiveRegionFullCompanionPrecision regions hd hM rho
    spacing epsilon background chain fineSmall
  have hactive := cmp99SourceActiveRegionFullCompanionPrecision_compression
    regions hd hM rho spacing epsilon background chain fineSmall
  apply ContinuousLinearMap.ext
  intro phi
  apply PiLp.ext
  intro x
  have hpoint := congrArg (fun psi => psi x)
    (congrArg
      (fun A : ActiveGaugeZeroCochain Omega (SUNLieCoord Nc) →L[ℝ]
        ActiveGaugeZeroCochain Omega (SUNLieCoord Nc) => A phi)
      hactive)
  simpa [cmp99RegionalDirichletPrecision,
    cmp99SourceActiveRegionFullCompanionAmbientPrecision,
    finitePiLpTypedKernelReindex, cmp99SourceFullActiveRegionSiteEquiv,
    R, E, Kfull, cmp99NestedActiveRegionRestriction,
    cmp99NestedActiveRegionExtension,
    LinearIsometryEquiv.piLpCongrLeft_apply, Equiv.piCongrLeft'] using hpoint

end

end YangMills.RG
