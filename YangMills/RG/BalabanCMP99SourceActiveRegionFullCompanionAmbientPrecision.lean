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

/-- Reindexing an ambient field to the literal full active carrier is exactly
restriction to that carrier.  This is the source-leg bridge used by the
ambient full-companion compression; it is not left to definitional
reduction. -/
theorem cmp99SourceFullActiveRegion_restrictZero_eq_reindex
    {g : Type*} [NormedAddCommGroup g] [InnerProductSpace ℝ g]
    [FiniteDimensional ℝ g] :
    (restrictZeroCLM (𝔤 := g) (cmp99SourceFullActiveRegion d N)) =
      (LinearIsometryEquiv.piLpCongrLeft 2 ℝ g
        (cmp99SourceFullActiveRegionSiteEquiv d N).symm).toContinuousLinearEquiv := by
  apply ContinuousLinearMap.ext
  intro phi
  apply PiLp.ext
  intro x
  rfl

/-- Reindexing a field from the literal full active carrier to the ambient
box is exactly zero extension.  Fullness discharges the only support branch
explicitly. -/
theorem cmp99SourceFullActiveRegion_extendZero_eq_reindex
    {g : Type*} [NormedAddCommGroup g] [InnerProductSpace ℝ g]
    [FiniteDimensional ℝ g] :
    (extendZeroZeroCLM (𝔤 := g) (cmp99SourceFullActiveRegion d N)) =
      (LinearIsometryEquiv.piLpCongrLeft 2 ℝ g
        (cmp99SourceFullActiveRegionSiteEquiv d N)).toContinuousLinearEquiv := by
  apply ContinuousLinearMap.ext
  intro phi
  apply PiLp.ext
  intro x
  change (if hx : x ∈ (cmp99SourceFullActiveRegion d N).sites then
      phi ⟨x, hx⟩ else 0) =
    phi ((cmp99SourceFullActiveRegionSiteEquiv d N).symm x)
  simp [cmp99SourceFullActiveRegion, cmp99SourceFullActiveRegionSiteEquiv]

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

/-- Dirichlet compression on an arbitrary finite ambient carrier.  The older
`cmp99RegionalDirichletPrecision` is specialized to the later
`FinBox 4 (M * (2 * Q))` geometry; the source C6d chain instead lives first
on `FinBox d N`, so the carrier parameters must remain explicit here. -/
noncomputable def cmp99SourceAmbientDirichletPrecision
    {g : Type*} [NormedAddCommGroup g] [InnerProductSpace ℝ g]
    [FiniteDimensional ℝ g]
    (Omega : ActiveGaugeRegion d N)
    (K : GaugeZeroCochain d N g →L[ℝ] GaugeZeroCochain d N g) :
    ActiveGaugeZeroCochain Omega g →L[ℝ]
      ActiveGaugeZeroCochain Omega g :=
  (restrictZeroCLM (𝔤 := g) Omega).comp
    (K.comp (extendZeroZeroCLM (𝔤 := g) Omega))

/-- Ambient coercivity descends to the generic Dirichlet compression without
changing its floor. -/
theorem isCoerciveCLM_cmp99SourceAmbientDirichletPrecision
    {g : Type*} [NormedAddCommGroup g] [InnerProductSpace ℝ g]
    [FiniteDimensional ℝ g]
    (Omega : ActiveGaugeRegion d N)
    (K : GaugeZeroCochain d N g →L[ℝ] GaugeZeroCochain d N g)
    {c : ℝ} (hK : IsCoerciveCLM K c) :
    IsCoerciveCLM (cmp99SourceAmbientDirichletPrecision Omega K) c := by
  intro phi
  let E := extendZeroZeroCLM (𝔤 := g) Omega
  let R := restrictZeroCLM (𝔤 := g) Omega
  have hR : R = E.adjoint :=
    cmp99ActiveRegion_restrictZero_eq_extendZero_adjoint Omega
  have hambient := hK (E phi)
  rw [norm_extendZeroZeroCLM_eq Omega phi] at hambient
  change c * ‖phi‖ ^ 2 ≤ inner ℝ phi (R (K (E phi)))
  rw [hR, ContinuousLinearMap.adjoint_inner_right]
  exact hambient

/-- The ambient reindexing preserves the full-companion coercivity floor
exactly. -/
theorem isCoerciveCLM_cmp99SourceActiveRegionFullCompanionAmbientPrecision
    {Omega : ActiveGaugeRegion d N} {depth : ℕ}
    (regions : CMP99SourceActiveRegionChain d M N Omega depth)
    (hd : 2 ≤ d) (hM : 2 ≤ M) (hdepth : 0 < depth)
    {spacing epsilon : ℝ}
    (hspacing : 0 < spacing)
    (background : GaugeConfig d N (SUN Nc))
    (chain : CMP99SourceUbarRadiusChain d M Nc depth epsilon)
    (fineSmall : ∀ e : ConcreteEdge d N,
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff d M depth spacing epsilon < 1) :
    let T := cmp99SourceActiveRegionFullCompanionTower
      (d := d) (M := M) (N := N) (Nc := Nc) (Omega := Omega)
      (depth := depth) regions hd hM (matrixSUNAdjointModel Nc) spacing epsilon
      background chain fineSmall
    IsCoerciveCLM
      (cmp99SourceActiveRegionFullCompanionAmbientPrecision
        (d := d) (M := M) (N := N) (Nc := Nc) (Omega := Omega)
        (depth := depth) regions hd hM (matrixSUNAdjointModel Nc) spacing epsilon
        background chain fineSmall)
      (cmp99SourceActiveRegionTerminalPhysicalCoercivity T M depth epsilon) := by
  exact isCoerciveCLM_finitePiLpTypedKernelReindex
    (e := cmp99SourceFullActiveRegionSiteEquiv d N)
    (A := cmp99SourceActiveRegionFullCompanionPrecision
      (d := d) (M := M) (N := N) (Nc := Nc) (Omega := Omega)
      (depth := depth) regions hd hM (matrixSUNAdjointModel Nc) spacing epsilon
      background chain fineSmall)
    (isCoerciveCLM_cmp99SourceActiveRegionFullCompanionPrecision
      (d := d) (M := M) (N := N) (Nc := Nc) (Omega := Omega)
      (depth := depth) regions hd hM hdepth hspacing background chain fineSmall
      hsmall)

/-- Dirichlet compression after the explicit full-site reindexing is exactly
the regional source precision with its regional source-flow coefficient. -/
theorem cmp99SourceAmbientDirichletPrecision_fullCompanion_eq
    {Omega : ActiveGaugeRegion d N} {depth : ℕ}
    (regions : CMP99SourceActiveRegionChain d M N Omega depth)
    (hd : 2 ≤ d) (hM : 2 ≤ M) (rho : SUNAdjointModel Nc)
    (spacing epsilon : ℝ) (background : GaugeConfig d N (SUN Nc))
    (chain : CMP99SourceUbarRadiusChain d M Nc depth epsilon)
    (fineSmall : ∀ e : ConcreteEdge d N,
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon) :
    let Tregional := regions.weightedQprimeTower hd hM rho spacing epsilon
      background chain fineSmall
    cmp99SourceAmbientDirichletPrecision Omega
        (cmp99SourceActiveRegionFullCompanionAmbientPrecision
          (d := d) (M := M) (N := N) (Nc := Nc) (Omega := Omega)
          (depth := depth) regions hd hM rho spacing epsilon background chain
          fineSmall) =
      cmp99SourceGaugePrecision
        (cmp99ActiveRegionSourceCovariantLaplacian Omega rho background spacing)
        Tregional.Qprime
        (cmp99SourceActiveRegionTerminalPhysicalCountingCoefficient Tregional
          (cmp99SourceMassParameter 1 (M : ℝ) depth)) := by
  let R := cmp99NestedActiveRegionRestriction (g := SUNLieCoord Nc) Omega
    (cmp99SourceFullActiveRegion d N)
  let E := cmp99NestedActiveRegionExtension (g := SUNLieCoord Nc) Omega
    (cmp99SourceFullActiveRegion d N)
  let Kfull : ActiveGaugeZeroCochain (cmp99SourceFullActiveRegion d N)
        (SUNLieCoord Nc) →L[ℝ]
      ActiveGaugeZeroCochain (cmp99SourceFullActiveRegion d N)
        (SUNLieCoord Nc) :=
    cmp99SourceActiveRegionFullCompanionPrecision
      (d := d) (M := M) (N := N) (Nc := Nc) (Omega := Omega)
      (depth := depth) regions hd hM rho spacing epsilon background chain
      fineSmall
  have hactive := cmp99SourceActiveRegionFullCompanionPrecision_compression
    (d := d) (M := M) (N := N) (Nc := Nc) (Omega := Omega)
    (depth := depth) regions hd hM rho spacing epsilon background chain
    fineSmall
  apply ContinuousLinearMap.ext
  intro phi
  apply PiLp.ext
  intro x
  have hpoint := congrArg (fun psi => psi x)
    (congrArg
      (fun A : ActiveGaugeZeroCochain Omega (SUNLieCoord Nc) →L[ℝ]
        ActiveGaugeZeroCochain Omega (SUNLieCoord Nc) => A phi)
      hactive)
  simpa [cmp99SourceAmbientDirichletPrecision,
    cmp99SourceActiveRegionFullCompanionAmbientPrecision,
    finitePiLpTypedKernelReindex, cmp99SourceFullActiveRegionSiteEquiv,
    cmp99SourceFullActiveRegion_restrictZero_eq_reindex,
    cmp99SourceFullActiveRegion_extendZero_eq_reindex,
    R, E, Kfull, cmp99NestedActiveRegionRestriction,
    cmp99NestedActiveRegionExtension,
    LinearIsometryEquiv.piLpCongrLeft_apply, Equiv.piCongrLeft'] using hpoint

end

end YangMills.RG
