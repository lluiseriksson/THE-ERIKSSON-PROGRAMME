/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceFlatRetainedPhysicalTower
import YangMills.RG.BalabanCMP99SourceGeneratedQprimeRowMass

/-!
# Canonical flat recursion for the generated CMP99 `Q'` and `Q'^*`

PRE-VALIDATION: source is present, its `.olean` has not yet been materialized,
and the result has not yet been verified by the Lean compiler.

The generated physical tower already constructs every background and every
one-step average internally.  At the literal flat background, physical Ubar
preserves flatness.  This file uses that fact to identify the complete
coordinate-exposed recursion with a second recursion whose one-step transport
is definitionally the identity.  Thus neither a family of block averages nor
a family of weighted adjoints is supplied by the caller.

Honest scope: the endpoint is the exact multiscale recursion on the typed
active-region chain.  It does not collapse the recursion to one block average
of side `M^depth`, identify counting and source-weighted adjoints, construct a
Fourier transform, match the real generated precision with its separately
reconstructed flat complex precision, or produce a regional Green bound.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {d M N Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero N] [NeZero Nc]

/-- Identity transport on the real physical Lie-coordinate fibre. -/
def cmp99SourceFlatRealTransport {N' : ℕ} [NeZero N'] :
    FinBox d N' → FinBox d (M * N') →
      (SUNLieCoord Nc ≃ₗᵢ[ℝ] SUNLieCoord Nc) :=
  fun _ _ => LinearIsometryEquiv.refl ℝ (SUNLieCoord Nc)

omit [NeZero d] [NeZero M] [NeZero Nc] in
@[simp] theorem cmp99SourceFlatRealTransport_apply
    {N' : ℕ} [NeZero N'] (y : FinBox d N') (x : FinBox d (M * N'))
    (v : SUNLieCoord Nc) :
    cmp99SourceFlatRealTransport y x v = v := rfl

/-- Linkwise radius-zero smallness of the literal flat background, with the
matrix coercion exposed once for all recursive consumers. -/
theorem cmp99SourceFlatGaugeConfig_zero_small
    {N : ℕ} [NeZero N] :
    ∀ e : ConcreteEdge d N,
      ‖(cmp99SourceFlatGaugeConfig d N Nc e :
          Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ 0 := by
  intro e
  change ‖((1 : SUN Nc) : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ 0
  simp

/-- Every radius-zero normalized scale built on the literal flat background
has the literal flat next background, independently of the proof terms used
to certify nonnegativity, no winding, and fine-link smallness. -/
@[simp] theorem
    cmp99SourceNormalizedRegionalScale_ofFineSmall_flat_nextBackground
    {N' : ℕ} [NeZero N']
    (hd : 2 ≤ d) (hM : 2 ≤ M)
    (Omega : ActiveGaugeRegion d (M * N'))
    (blockSaturated : Omega.BlockSaturated)
    (epsilonFine_nonneg : 0 ≤ (0 : ℝ))
    (noWinding : cmp99SourceUbarFineDeviationRadius d M 0 <
      cmp99UbarNoWindingThreshold Nc)
    (fineSmall : ∀ e : ConcreteEdge d (M * N'),
      ‖(cmp99SourceFlatGaugeConfig d (M * N') Nc e :
          Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ 0) :
    (CMP99SourceNormalizedRegionalScale.ofFineSmall hd hM Omega
        (cmp99SourceFlatGaugeConfig d (M * N') Nc) blockSaturated
        0 epsilonFine_nonneg noWinding fineSmall).toSourceScale.data.nextBackground =
      cmp99SourceFlatGaugeConfig d N' Nc := by
  change
    cmp99PhysicalUbarGaugeConfigOfDeviationBudget
        (cmp99SourceFlatGaugeConfig d (M * N') Nc)
        (cmp99SourceBaseCoarseBackground
          (cmp99SourceFlatGaugeConfig d (M * N') Nc))
        _ _ _ _ _ =
      cmp99SourceFlatGaugeConfig d N' Nc
  exact cmp99PhysicalUbarGaugeConfigOfDeviationBudget_flat _ _ _ _ _

/-- The physical contour transport on a flat background is the explicit
identity transport as a complete family of fibre isometries. -/
theorem cmp99SourceWeightedPhysicalTransport_flat_eq_explicit
    {N' : ℕ} [NeZero N'] (rho : SUNAdjointModel Nc) :
    cmp99SourceWeightedPhysicalTransport rho
        (cmp99SourceFlatGaugeConfig d (M * N') Nc) =
      cmp99SourceFlatRealTransport := by
  funext y x
  exact cmp99SourceWeightedPhysicalTransport_flat_eq_refl rho y x

/-- The one-step source-normalized flat average, with no caller-supplied
transport family. -/
noncomputable def cmp99SourceFlatRealBlockAverageCLM
    {N' : ℕ} [NeZero N'] (Omega : ActiveGaugeRegion d (M * N')) :
    ActiveGaugeZeroCochain Omega (SUNLieCoord Nc) →L[ℝ]
      ActiveGaugeZeroCochain
        (cmp99ActiveCoarseRegion (M := M) (N' := N') Omega)
        (SUNLieCoord Nc) :=
  cmp99SourceTransportedBlockAverageCLM Omega
    (cmp99SourceFlatRealTransport (d := d) (M := M) (N' := N') (Nc := Nc))

/-- The coefficient-one flat weighted adjoint paired with the explicit flat
average. -/
noncomputable def cmp99SourceFlatRealBlockWeightedAdjointCLM
    {N' : ℕ} [NeZero N'] (Omega : ActiveGaugeRegion d (M * N'))
    (hOmega : Omega.BlockSaturated) :
    ActiveGaugeZeroCochain
        (cmp99ActiveCoarseRegion (M := M) (N' := N') Omega)
        (SUNLieCoord Nc) →L[ℝ]
      ActiveGaugeZeroCochain Omega (SUNLieCoord Nc) :=
  cmp99SourceTransportedBlockWeightedAdjointCLM Omega hOmega
    (cmp99SourceFlatRealTransport (d := d) (M := M) (N' := N') (Nc := Nc))

/-- The literal physical one-step average at the flat background is the
explicit identity-transport average. -/
theorem cmp99SourceTransportedBlockAverageCLM_flat_eq_explicit
    {N' : ℕ} [NeZero N'] (Omega : ActiveGaugeRegion d (M * N'))
    (rho : SUNAdjointModel Nc) :
    cmp99SourceTransportedBlockAverageCLM Omega
        (cmp99SourceWeightedPhysicalTransport rho
          (cmp99SourceFlatGaugeConfig d (M * N') Nc)) =
      cmp99SourceFlatRealBlockAverageCLM Omega := by
  rw [cmp99SourceWeightedPhysicalTransport_flat_eq_explicit]
  rfl

/-- The literal physical one-step weighted adjoint at the flat background is
the explicit identity-transport synthesis. -/
theorem cmp99SourceTransportedBlockWeightedAdjointCLM_flat_eq_explicit
    {N' : ℕ} [NeZero N'] (Omega : ActiveGaugeRegion d (M * N'))
    (hOmega : Omega.BlockSaturated) (rho : SUNAdjointModel Nc) :
    cmp99SourceTransportedBlockWeightedAdjointCLM Omega hOmega
        (cmp99SourceWeightedPhysicalTransport rho
          (cmp99SourceFlatGaugeConfig d (M * N') Nc)) =
      cmp99SourceFlatRealBlockWeightedAdjointCLM Omega hOmega := by
  rw [cmp99SourceWeightedPhysicalTransport_flat_eq_explicit]
  rfl

/-- The complete explicit flat `Q'` recursion on one typed region chain. -/
noncomputable def CMP99SourceActiveRegionChain.flatExplicitQprime
    {N depth : ℕ} {Omega : ActiveGaugeRegion d N}
    (regions : CMP99SourceActiveRegionChain d M N Omega depth) :
    letI : NeZero N := regions.neZero
    ActiveGaugeZeroCochain Omega (SUNLieCoord Nc) →L[ℝ]
      PiLp 2 (fun _ : regions.terminalSite => SUNLieCoord Nc) := by
  letI : NeZero N := regions.neZero
  induction regions with
  | stop Omega =>
      exact ContinuousLinearMap.id ℝ _
  | @step N' depth _ Omega hOmega tail ih =>
      letI : NeZero (M * N') := inferInstance
      exact ih.comp (cmp99SourceFlatRealBlockAverageCLM Omega)

/-- The reverse coefficient-one synthesis recursion paired with
`flatExplicitQprime`. -/
noncomputable def CMP99SourceActiveRegionChain.flatExplicitWeightedAdjoint
    {N depth : ℕ} {Omega : ActiveGaugeRegion d N}
    (regions : CMP99SourceActiveRegionChain d M N Omega depth) :
    letI : NeZero N := regions.neZero
    PiLp 2 (fun _ : regions.terminalSite => SUNLieCoord Nc) →L[ℝ]
      ActiveGaugeZeroCochain Omega (SUNLieCoord Nc) := by
  letI : NeZero N := regions.neZero
  induction regions with
  | stop Omega =>
      exact ContinuousLinearMap.id ℝ _
  | @step N' depth _ Omega hOmega tail ih =>
      letI : NeZero (M * N') := inferInstance
      exact (cmp99SourceFlatRealBlockWeightedAdjointCLM Omega hOmega).comp ih

/-- Specialization of the internally generated physical `Q'` recursion to the
literal flat background and the canonical zero-radius chain. -/
noncomputable def CMP99SourceActiveRegionChain.flatPhysicalQprime
    {N depth : ℕ} {Omega : ActiveGaugeRegion d N}
    (regions : CMP99SourceActiveRegionChain d M N Omega depth)
    (hd : 2 ≤ d) (hM : 2 ≤ M) (rho : SUNAdjointModel Nc) (spacing : ℝ) :
    letI : NeZero N := regions.neZero
    ActiveGaugeZeroCochain Omega (SUNLieCoord Nc) →L[ℝ]
      PiLp 2 (fun _ : regions.terminalSite => SUNLieCoord Nc) := by
  letI : NeZero N := regions.neZero
  exact regions.physicalQprime hd hM rho spacing 0
    (cmp99SourceFlatGaugeConfig d N Nc)
    (cmp99SourceFlatZeroRadiusChain depth)
    cmp99SourceFlatGaugeConfig_zero_small

/-- Specialization of the internally generated physical weighted adjoint to
the same literal flat data. -/
noncomputable def CMP99SourceActiveRegionChain.flatPhysicalWeightedAdjoint
    {N depth : ℕ} {Omega : ActiveGaugeRegion d N}
    (regions : CMP99SourceActiveRegionChain d M N Omega depth)
    (hd : 2 ≤ d) (hM : 2 ≤ M) (rho : SUNAdjointModel Nc) (spacing : ℝ) :
    letI : NeZero N := regions.neZero
    PiLp 2 (fun _ : regions.terminalSite => SUNLieCoord Nc) →L[ℝ]
      ActiveGaugeZeroCochain Omega (SUNLieCoord Nc) := by
  letI : NeZero N := regions.neZero
  exact regions.physicalWeightedAdjoint hd hM rho spacing 0
    (cmp99SourceFlatGaugeConfig d N Nc)
    (cmp99SourceFlatZeroRadiusChain depth)
    cmp99SourceFlatGaugeConfig_zero_small

/-- Every internally generated flat physical average is exactly the explicit
identity-transport recursion.  Flatness of every hidden intermediate
background is derived from physical Ubar, not assumed as a family. -/
theorem CMP99SourceActiveRegionChain.flatPhysicalQprime_eq_explicit
    {N depth : ℕ} {Omega : ActiveGaugeRegion d N}
    (regions : CMP99SourceActiveRegionChain d M N Omega depth)
    (hd : 2 ≤ d) (hM : 2 ≤ M) (rho : SUNAdjointModel Nc) :
    letI : NeZero N := regions.neZero
    ∀ spacing : ℝ,
      regions.flatPhysicalQprime hd hM rho spacing =
        regions.flatExplicitQprime := by
  letI : NeZero N := regions.neZero
  induction regions with
  | stop Omega =>
      intro spacing
      rfl
  | @step N' depth _ Omega hOmega tail ih =>
      intro spacing
      letI : NeZero (M * N') := inferInstance
      let Scale := cmp99SourceFlatNormalizedRegionalScale
        (Nc := Nc) hd hM Omega hOmega
      have htail := ih ((M : ℝ) * spacing)
      have htail' := htail
      simp only [CMP99SourceActiveRegionChain.flatPhysicalQprime,
        CMP99SourceActiveRegionChain.physicalQprime,
        CMP99SourceActiveRegionChain.flatExplicitQprime] at htail'
      have nextSmall : ∀ e : ConcreteEdge d N',
          ‖(Scale.toSourceScale.data.nextBackground e :
              Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ 0 := by
        rw [cmp99SourceFlatNormalizedRegionalScale_nextBackground]
        exact cmp99SourceFlatGaugeConfig_zero_small
      simp only [CMP99SourceActiveRegionChain.flatPhysicalQprime,
        CMP99SourceActiveRegionChain.physicalQprime,
        CMP99SourceActiveRegionChain.flatExplicitQprime]
      rw [cmp99SourceTransportedBlockAverageCLM_flat_eq_explicit]
      apply congrArg
        (fun T :
            ActiveGaugeZeroCochain
                (cmp99ActiveCoarseRegion (M := M) (N' := N') Omega)
                (SUNLieCoord Nc) →L[ℝ]
              PiLp 2 (fun _ : tail.terminalSite => SUNLieCoord Nc) =>
          T.comp (cmp99SourceFlatRealBlockAverageCLM Omega))
      have hradius : cmp99SourceUbarNextFineRadius d M 0 = 0 :=
        cmp99SourceUbarNextFineRadius_zero
      cases hradius
      have hbackground :
          Scale.toSourceScale.data.nextBackground =
            cmp99SourceFlatGaugeConfig d N' Nc := by
        simpa only [Scale] using
          cmp99SourceFlatNormalizedRegionalScale_nextBackground
            (Nc := Nc) hd hM Omega hOmega
      cases hbackground
      exact htail'

/-- The generated coefficient-one physical synthesis is likewise exactly the
explicit reverse flat recursion. -/
theorem CMP99SourceActiveRegionChain.flatPhysicalWeightedAdjoint_eq_explicit
    {N depth : ℕ} {Omega : ActiveGaugeRegion d N}
    (regions : CMP99SourceActiveRegionChain d M N Omega depth)
    (hd : 2 ≤ d) (hM : 2 ≤ M) (rho : SUNAdjointModel Nc) :
    letI : NeZero N := regions.neZero
    ∀ spacing : ℝ,
      regions.flatPhysicalWeightedAdjoint hd hM rho spacing =
        regions.flatExplicitWeightedAdjoint := by
  letI : NeZero N := regions.neZero
  induction regions with
  | stop Omega =>
      intro spacing
      rfl
  | @step N' depth _ Omega hOmega tail ih =>
      intro spacing
      letI : NeZero (M * N') := inferInstance
      let Scale := cmp99SourceFlatNormalizedRegionalScale
        (Nc := Nc) hd hM Omega hOmega
      have htail := ih ((M : ℝ) * spacing)
      have htail' := htail
      simp only [CMP99SourceActiveRegionChain.flatPhysicalWeightedAdjoint,
        CMP99SourceActiveRegionChain.physicalWeightedAdjoint,
        CMP99SourceActiveRegionChain.flatExplicitWeightedAdjoint] at htail'
      have nextSmall : ∀ e : ConcreteEdge d N',
          ‖(Scale.toSourceScale.data.nextBackground e :
              Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ 0 := by
        rw [cmp99SourceFlatNormalizedRegionalScale_nextBackground]
        exact cmp99SourceFlatGaugeConfig_zero_small
      simp only [CMP99SourceActiveRegionChain.flatPhysicalWeightedAdjoint,
        CMP99SourceActiveRegionChain.physicalWeightedAdjoint,
        CMP99SourceActiveRegionChain.flatExplicitWeightedAdjoint]
      rw [cmp99SourceTransportedBlockWeightedAdjointCLM_flat_eq_explicit]
      apply congrArg
        (fun T :
            PiLp 2 (fun _ : tail.terminalSite => SUNLieCoord Nc) →L[ℝ]
              ActiveGaugeZeroCochain
                (cmp99ActiveCoarseRegion (M := M) (N' := N') Omega)
                (SUNLieCoord Nc) =>
          (cmp99SourceFlatRealBlockWeightedAdjointCLM Omega hOmega).comp T)
      have hradius : cmp99SourceUbarNextFineRadius d M 0 = 0 :=
        cmp99SourceUbarNextFineRadius_zero
      cases hradius
      have hbackground :
          Scale.toSourceScale.data.nextBackground =
            cmp99SourceFlatGaugeConfig d N' Nc := by
        simpa only [Scale] using
          cmp99SourceFlatNormalizedRegionalScale_nextBackground
            (Nc := Nc) hd hM Omega hOmega
      cases hbackground
      exact htail'

end

end YangMills.RG
