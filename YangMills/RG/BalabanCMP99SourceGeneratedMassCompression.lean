import YangMills.RG.BalabanCMP99SourceActiveRegionFullCompanion
import YangMills.RG.BalabanCMP99SourceGeneratedNestedRestrictionAdjoint

/-!
PRE-VALIDATION: source present; `.olean` not yet materialized and the result
has not yet been verified by the compiler or axiom oracle.

# Exact Dirichlet compression of the generated counting mass

For nested typed source-region chains, restriction followed by literal zero
extension is the identity on the smaller fine carrier.  Combining that fact
with the already proved transition law for the complete recursively generated
counting mass gives its exact Dirichlet compression.

This file treats only the `Q'^* Q'` mass.  It does not identify the ambient
and regional covariant Laplacians, construct a Green operator, or discharge
an Eq. (3.42) bound.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator RealInnerProductSpace

noncomputable section

variable {d M N Nc : ℕ} [NeZero d] [NeZero M] [NeZero N] [NeZero Nc]

omit [NeZero d] in
/-- Restriction from a larger active region followed by literal zero
extension from a nested smaller region is the identity on the smaller
counting-Hilbert space. -/
theorem cmp99NestedActiveRegionRestriction_comp_extension_eq_id
    {g : Type*} [NormedAddCommGroup g] [InnerProductSpace ℝ g]
    [FiniteDimensional ℝ g]
    (OmegaSmall OmegaLarge : ActiveGaugeRegion d N)
    (hsub : OmegaSmall.sites ⊆ OmegaLarge.sites) :
    (cmp99NestedActiveRegionRestriction (g := g)
      OmegaSmall OmegaLarge).comp
        (cmp99NestedActiveRegionExtension (g := g)
          OmegaSmall OmegaLarge) =
      ContinuousLinearMap.id ℝ (ActiveGaugeZeroCochain OmegaSmall g) := by
  apply ContinuousLinearMap.ext
  intro phi
  apply PiLp.ext
  intro x
  simp only [cmp99NestedActiveRegionRestriction,
    cmp99NestedActiveRegionExtension, ContinuousLinearMap.comp_apply]
  change (if hLarge : x.1 ∈ OmegaLarge.sites then
      (if hSmall : x.1 ∈ OmegaSmall.sites then phi ⟨x.1, hSmall⟩ else 0)
    else 0) = phi x
  rw [dif_pos (hsub x.2), dif_pos x.2]

/-- Exact compression of the complete recursively generated counting mass
along any typed nesting of source-region chains. -/
theorem CMP99SourceNestedRegionChains.generatedCountingMass_compression
    {OmegaSmall OmegaLarge : ActiveGaugeRegion d N} {depth : ℕ}
    {regionsSmall : CMP99SourceActiveRegionChain d M N OmegaSmall depth}
    {regionsLarge : CMP99SourceActiveRegionChain d M N OmegaLarge depth}
    (H : CMP99SourceNestedRegionChains d M regionsSmall regionsLarge)
    (hsub : OmegaSmall.sites ⊆ OmegaLarge.sites)
    (hd : 2 ≤ d) (hM : 2 ≤ M) (rho : SUNAdjointModel Nc)
    (spacing epsilon : ℝ) (background : GaugeConfig d N (SUN Nc))
    (chain : CMP99SourceUbarRadiusChain d M Nc depth epsilon)
    (fineSmall : ∀ e : ConcreteEdge d N,
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon) :
    let R := cmp99NestedActiveRegionRestriction (g := SUNLieCoord Nc)
      OmegaSmall OmegaLarge
    let E := cmp99NestedActiveRegionExtension (g := SUNLieCoord Nc)
      OmegaSmall OmegaLarge
    R.comp ((regionsLarge.generatedCountingMass hd hM rho spacing epsilon
      background chain fineSmall).comp E) =
      regionsSmall.generatedCountingMass hd hM rho spacing epsilon
        background chain fineSmall := by
  let R := cmp99NestedActiveRegionRestriction (g := SUNLieCoord Nc)
    OmegaSmall OmegaLarge
  let E := cmp99NestedActiveRegionExtension (g := SUNLieCoord Nc)
    OmegaSmall OmegaLarge
  let massSmall := regionsSmall.generatedCountingMass hd hM rho spacing
    epsilon background chain fineSmall
  let massLarge := regionsLarge.generatedCountingMass hd hM rho spacing
    epsilon background chain fineSmall
  have htransition : R.comp massLarge = massSmall.comp R := by
    simpa [R, massSmall, massLarge] using
      H.generatedCountingMass_transition hd hM rho spacing epsilon background
        chain fineSmall
  have hRE : R.comp E =
      ContinuousLinearMap.id ℝ
        (ActiveGaugeZeroCochain OmegaSmall (SUNLieCoord Nc)) := by
    exact cmp99NestedActiveRegionRestriction_comp_extension_eq_id
      OmegaSmall OmegaLarge hsub
  apply ContinuousLinearMap.ext
  intro phi
  have ht := congrArg
    (fun A : ActiveGaugeZeroCochain OmegaLarge (SUNLieCoord Nc) →L[ℝ]
        ActiveGaugeZeroCochain OmegaSmall (SUNLieCoord Nc) => A (E phi))
    htransition
  have hre := congrArg
    (fun A : ActiveGaugeZeroCochain OmegaSmall (SUNLieCoord Nc) →L[ℝ]
        ActiveGaugeZeroCochain OmegaSmall (SUNLieCoord Nc) => A phi) hRE
  simpa [R, E, massSmall, massLarge, ContinuousLinearMap.comp_apply] using
    ht.trans (congrArg massSmall hre)

/-- The same compression stated for the literal generated `Q'^* Q'` masses
used by the source gauge precision. -/
theorem CMP99SourceNestedRegionChains.QprimeMass_compression
    {OmegaSmall OmegaLarge : ActiveGaugeRegion d N} {depth : ℕ}
    {regionsSmall : CMP99SourceActiveRegionChain d M N OmegaSmall depth}
    {regionsLarge : CMP99SourceActiveRegionChain d M N OmegaLarge depth}
    (H : CMP99SourceNestedRegionChains d M regionsSmall regionsLarge)
    (hsub : OmegaSmall.sites ⊆ OmegaLarge.sites)
    (hd : 2 ≤ d) (hM : 2 ≤ M) (rho : SUNAdjointModel Nc)
    (spacing epsilon : ℝ) (background : GaugeConfig d N (SUN Nc))
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
    R.comp ((Tlarge.Qprime.adjoint.comp Tlarge.Qprime).comp E) =
      Tsmall.Qprime.adjoint.comp Tsmall.Qprime := by
  simp only
  rw [← regionsLarge.generatedCountingMass_eq_QprimeMass hd hM rho spacing
      epsilon background chain fineSmall,
    ← regionsSmall.generatedCountingMass_eq_QprimeMass hd hM rho spacing
      epsilon background chain fineSmall]
  exact H.generatedCountingMass_compression hsub hd hM rho spacing epsilon
    background chain fineSmall

end

end YangMills.RG
