import YangMills.RG.BalabanCMP99SourceGeneratedMassCompression
import YangMills.RG.BalabanCMP99SourceGeneratedLaplacianTransitionSupport

/-!
PRE-VALIDATION: source present; `.olean` not yet materialized and the result
has not yet been verified by the compiler or axiom oracle.

# Exact compression of the generated source precision

The two species of the source precision remain separate until the endpoint.
The nearest-neighbour covariant Laplacian compresses because literal zero
extension from the smaller carrier agrees with extension through the larger
carrier.  The complete generated `Q'^* Q'` mass compresses by its independent
transition theorem.  Their literal sum then compresses with the same printed
coefficient.

This is an active-carrier theorem.  Identifying the full active carrier with
the ordinary ambient `FinBox`, and identifying a concrete C6d chain with the
smaller input, remain separate dictionaries.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator RealInnerProductSpace

noncomputable section

variable {d M N Nc : ℕ} [NeZero d] [NeZero M] [NeZero N] [NeZero Nc]

omit [NeZero d] in
/-- Extending a field through a nested larger active carrier is exactly the
same ambient field as extending it directly from the smaller carrier. -/
theorem cmp99NestedActiveRegionExtension_extendZero_eq
    {g : Type*} [NormedAddCommGroup g] [InnerProductSpace ℝ g]
    [FiniteDimensional ℝ g]
    (OmegaSmall OmegaLarge : ActiveGaugeRegion d N)
    (hsub : OmegaSmall.sites ⊆ OmegaLarge.sites)
    (phi : ActiveGaugeZeroCochain OmegaSmall g) :
    extendZeroZeroCLM OmegaLarge
        (cmp99NestedActiveRegionExtension OmegaSmall OmegaLarge phi) =
      extendZeroZeroCLM OmegaSmall phi := by
  apply PiLp.ext
  intro x
  by_cases hxSmall : x ∈ OmegaSmall.sites
  · have hxLarge : x ∈ OmegaLarge.sites := hsub hxSmall
    simp [cmp99NestedActiveRegionExtension, hxSmall, hxLarge]
  · by_cases hxLarge : x ∈ OmegaLarge.sites
    · simp [cmp99NestedActiveRegionExtension, hxSmall, hxLarge]
    · simp [cmp99NestedActiveRegionExtension, hxSmall, hxLarge]

/-- The regional covariant Laplacian is the exact nested Dirichlet
compression of the same larger-region Laplacian. -/
theorem cmp99ActiveRegionSourceCovariantLaplacian_nested_compression_eq
    (OmegaSmall OmegaLarge : ActiveGaugeRegion d N)
    (hsub : OmegaSmall.sites ⊆ OmegaLarge.sites)
    (rho : SUNAdjointModel Nc) (background : PhysicalGaugeBackground d N Nc)
    (spacing : ℝ) :
    let R := cmp99NestedActiveRegionRestriction (g := SUNLieCoord Nc)
      OmegaSmall OmegaLarge
    let E := cmp99NestedActiveRegionExtension (g := SUNLieCoord Nc)
      OmegaSmall OmegaLarge
    R.comp ((cmp99ActiveRegionSourceCovariantLaplacian OmegaLarge rho
      background spacing).comp E) =
      cmp99ActiveRegionSourceCovariantLaplacian OmegaSmall rho background
        spacing := by
  let R := cmp99NestedActiveRegionRestriction (g := SUNLieCoord Nc)
    OmegaSmall OmegaLarge
  let E := cmp99NestedActiveRegionExtension (g := SUNLieCoord Nc)
    OmegaSmall OmegaLarge
  apply ContinuousLinearMap.ext
  intro phi
  apply PiLp.ext
  intro x
  have hxLarge : x.1 ∈ OmegaLarge.sites := hsub x.2
  let xLarge : ActiveGaugeRegion.Site OmegaLarge := ⟨x.1, hxLarge⟩
  have hLarge := congrArg (fun psi => psi xLarge)
    (cmp99ActiveRegionSourceCovariantLaplacian_apply_eq_compression
      OmegaLarge rho background spacing (E phi))
  have hSmall := congrArg (fun psi => psi x)
    (cmp99ActiveRegionSourceCovariantLaplacian_apply_eq_compression
      OmegaSmall rho background spacing phi)
  have hExt := cmp99NestedActiveRegionExtension_extendZero_eq
    OmegaSmall OmegaLarge hsub phi
  change (if h : x.1 ∈ OmegaLarge.sites then
      cmp99ActiveRegionSourceCovariantLaplacian OmegaLarge rho background
        spacing (E phi) ⟨x.1, h⟩ else 0) =
    cmp99ActiveRegionSourceCovariantLaplacian OmegaSmall rho background
      spacing phi x
  rw [dif_pos hxLarge]
  change cmp99ActiveRegionSourceCovariantLaplacian OmegaLarge rho background
      spacing (E phi) xLarge =
    cmp99ActiveRegionSourceCovariantLaplacian OmegaSmall rho background
      spacing phi x
  rw [hLarge, hSmall, hExt]

/-- Exact nested compression of the complete generated source precision.
The Laplacian and mass equalities are invoked independently before their
literal sum is reassembled. -/
theorem CMP99SourceNestedRegionChains.sourceGaugePrecision_compression
    {OmegaSmall OmegaLarge : ActiveGaugeRegion d N} {depth : ℕ}
    {regionsSmall : CMP99SourceActiveRegionChain d M N OmegaSmall depth}
    {regionsLarge : CMP99SourceActiveRegionChain d M N OmegaLarge depth}
    (H : CMP99SourceNestedRegionChains d M regionsSmall regionsLarge)
    (hsub : OmegaSmall.sites ⊆ OmegaLarge.sites)
    (hd : 2 ≤ d) (hM : 2 ≤ M) (rho : SUNAdjointModel Nc)
    (spacing epsilon a : ℝ) (background : GaugeConfig d N (SUN Nc))
    (chain : CMP99SourceUbarRadiusChain d M Nc depth epsilon)
    (fineSmall : ∀ e : ConcreteEdge d N,
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon) :
    let Tsmall := regionsSmall.weightedQprimeTower hd hM rho spacing epsilon
      background chain fineSmall
    let Tlarge := regionsLarge.weightedQprimeTower hd hM rho spacing epsilon
      background chain fineSmall
    let R := cmp99NestedActiveRegionRestriction (g := SUNLieCoord Nc)
      OmegaSmall OmegaLarge
    let E := cmp99NestedActiveRegionExtension (g := SUNLieCoord Nc)
      OmegaSmall OmegaLarge
    let Ksmall := cmp99SourceGaugePrecision
      (cmp99ActiveRegionSourceCovariantLaplacian OmegaSmall rho background
        spacing) Tsmall.Qprime a
    let Klarge := cmp99SourceGaugePrecision
      (cmp99ActiveRegionSourceCovariantLaplacian OmegaLarge rho background
        spacing) Tlarge.Qprime a
    R.comp (Klarge.comp E) = Ksmall := by
  let Tsmall := regionsSmall.weightedQprimeTower hd hM rho spacing epsilon
    background chain fineSmall
  let Tlarge := regionsLarge.weightedQprimeTower hd hM rho spacing epsilon
    background chain fineSmall
  let R := cmp99NestedActiveRegionRestriction (g := SUNLieCoord Nc)
    OmegaSmall OmegaLarge
  let E := cmp99NestedActiveRegionExtension (g := SUNLieCoord Nc)
    OmegaSmall OmegaLarge
  let Lsmall := cmp99ActiveRegionSourceCovariantLaplacian OmegaSmall rho
    background spacing
  let Llarge := cmp99ActiveRegionSourceCovariantLaplacian OmegaLarge rho
    background spacing
  have hL : R.comp (Llarge.comp E) = Lsmall := by
    simpa [R, E, Lsmall, Llarge] using
      cmp99ActiveRegionSourceCovariantLaplacian_nested_compression_eq
        OmegaSmall OmegaLarge hsub rho background spacing
  have hQ : R.comp ((Tlarge.Qprime.adjoint.comp Tlarge.Qprime).comp E) =
      Tsmall.Qprime.adjoint.comp Tsmall.Qprime := by
    simpa [R, E, Tsmall, Tlarge] using
      H.QprimeMass_compression hsub hd hM rho spacing epsilon background chain
        fineSmall
  apply ContinuousLinearMap.ext
  intro phi
  have hLphi := congrArg
    (fun A : ActiveGaugeZeroCochain OmegaSmall (SUNLieCoord Nc) →L[ℝ]
        ActiveGaugeZeroCochain OmegaSmall (SUNLieCoord Nc) => A phi) hL
  have hQphi := congrArg
    (fun A : ActiveGaugeZeroCochain OmegaSmall (SUNLieCoord Nc) →L[ℝ]
        ActiveGaugeZeroCochain OmegaSmall (SUNLieCoord Nc) => A phi) hQ
  simp only [cmp99SourceGaugePrecision, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, map_add,
    map_smul]
  rw [hLphi, hQphi]

end

end YangMills.RG
