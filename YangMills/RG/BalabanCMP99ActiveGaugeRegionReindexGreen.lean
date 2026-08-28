import YangMills.RG.BalabanCMP99ActiveGaugeRegionReindex
import YangMills.RG.FinitePiLpTypedKernelReindexAlgebra

/-!
PRE-VALIDATION: source present; `.olean` not yet materialized in a fresh cold checkout, and the result is not compiler-verified for sealing.  Canonical Green transport across the explicit ambient
and localized carrier equivalences.  No compiler or axiom-oracle verdict is
claimed.
-/

namespace YangMills.RG

open YangMills

noncomputable section

variable {d N N' : ℕ} [NeZero d] [NeZero N] [NeZero N']

/-- Canonical Green of the generic ambient Dirichlet compression.  The Green
is generated from ambient coercivity; it is not caller data. -/
noncomputable def cmp99SourceAmbientDirichletGreen
    {g : Type*} [NormedAddCommGroup g] [InnerProductSpace ℝ g]
    [FiniteDimensional ℝ g]
    (Omega : ActiveGaugeRegion d N)
    (K : GaugeZeroCochain d N g →L[ℝ] GaugeZeroCochain d N g)
    {c : ℝ} (hc : 0 < c) (hK : IsCoerciveCLM K c) :
    ActiveGaugeZeroCochain Omega g →L[ℝ]
      ActiveGaugeZeroCochain Omega g :=
  covarianceOfIsCoerciveCLM
    (E := ActiveGaugeZeroCochain Omega g)
    (cmp99SourceAmbientDirichletPrecision
      (d := d) (N := N) (g := g) Omega K) hc
    (isCoerciveCLM_cmp99SourceAmbientDirichletPrecision
      (d := d) (N := N) (g := g) Omega K hK)

/-- The internally generated generic Dirichlet Green is a left inverse. -/
theorem cmp99SourceAmbientDirichletGreen_comp_precision
    {g : Type*} [NormedAddCommGroup g] [InnerProductSpace ℝ g]
    [FiniteDimensional ℝ g]
    (Omega : ActiveGaugeRegion d N)
    (K : GaugeZeroCochain d N g →L[ℝ] GaugeZeroCochain d N g)
    {c : ℝ} (hc : 0 < c) (hK : IsCoerciveCLM K c) :
    (cmp99SourceAmbientDirichletGreen Omega K hc hK).comp
        (cmp99SourceAmbientDirichletPrecision Omega K) =
      ContinuousLinearMap.id ℝ (ActiveGaugeZeroCochain Omega g) := by
  exact covarianceOfIsCoerciveCLM_comp_precision _ hc _

/-- The internally generated generic Dirichlet Green is a right inverse. -/
theorem cmp99SourceAmbientDirichletPrecision_comp_green
    {g : Type*} [NormedAddCommGroup g] [InnerProductSpace ℝ g]
    [FiniteDimensional ℝ g]
    (Omega : ActiveGaugeRegion d N)
    (K : GaugeZeroCochain d N g →L[ℝ] GaugeZeroCochain d N g)
    {c : ℝ} (hc : 0 < c) (hK : IsCoerciveCLM K c) :
    (cmp99SourceAmbientDirichletPrecision Omega K).comp
        (cmp99SourceAmbientDirichletGreen Omega K hc hK) =
      ContinuousLinearMap.id ℝ (ActiveGaugeZeroCochain Omega g) := by
  exact precision_comp_covarianceOfIsCoerciveCLM _ hc _

/-- The canonical Green commutes with simultaneous transport of the ambient
precision and localized carrier.  The conclusion is proved from coercive
inverse uniqueness; no Green equality is accepted as input. -/
theorem finitePiLpTypedKernelReindex_sourceAmbientDirichletGreen
    {g : Type*} [NormedAddCommGroup g] [InnerProductSpace ℝ g]
    [FiniteDimensional ℝ g]
    (e : FinBox d N ≃ FinBox d N') (Omega : ActiveGaugeRegion d N)
    (K : GaugeZeroCochain d N g →L[ℝ] GaugeZeroCochain d N g)
    {c : ℝ} (hc : 0 < c) (hK : IsCoerciveCLM K c) :
    finitePiLpTypedKernelReindex
        (cmp99ActiveGaugeRegionSiteReindexEquiv e Omega)
        (cmp99ActiveGaugeRegionSiteReindexEquiv e Omega)
        (cmp99SourceAmbientDirichletGreen Omega K hc hK) =
      cmp99SourceAmbientDirichletGreen
        (cmp99ActiveGaugeRegionReindex e Omega)
        (finitePiLpTypedKernelReindex e e K) hc
        (isCoerciveCLM_finitePiLpTypedKernelReindex e K hK) := by
  let E := cmp99ActiveGaugeRegionSiteReindexEquiv e Omega
  let A := cmp99SourceAmbientDirichletPrecision Omega K
  let A' := cmp99SourceAmbientDirichletPrecision
    (cmp99ActiveGaugeRegionReindex e Omega)
    (finitePiLpTypedKernelReindex e e K)
  let G := cmp99SourceAmbientDirichletGreen Omega K hc hK
  let hK' := isCoerciveCLM_finitePiLpTypedKernelReindex e K hK
  let hA' := isCoerciveCLM_cmp99SourceAmbientDirichletPrecision
    (cmp99ActiveGaugeRegionReindex e Omega)
    (finitePiLpTypedKernelReindex e e K) hK'
  let G' := cmp99SourceAmbientDirichletGreen
    (cmp99ActiveGaugeRegionReindex e Omega)
    (finitePiLpTypedKernelReindex e e K) hc hK'
  have hAG : A.comp G =
      ContinuousLinearMap.id ℝ (ActiveGaugeZeroCochain Omega g) := by
    exact cmp99SourceAmbientDirichletPrecision_comp_green Omega K hc hK
  have htransport :
      (finitePiLpTypedKernelReindex E E A).comp
          (finitePiLpTypedKernelReindex E E G) =
        ContinuousLinearMap.id ℝ
          (ActiveGaugeZeroCochain (cmp99ActiveGaugeRegionReindex e Omega) g) :=
    finitePiLpTypedKernelReindex_comp_eq_id E A G hAG
  have hAeq : finitePiLpTypedKernelReindex E E A = A' := by
    exact finitePiLpTypedKernelReindex_sourceAmbientDirichletPrecision
      e Omega K
  rw [hAeq] at htransport
  have hcanonical : A'.comp G' =
      ContinuousLinearMap.id ℝ
        (ActiveGaugeZeroCochain (cmp99ActiveGaugeRegionReindex e Omega) g) := by
    exact cmp99SourceAmbientDirichletPrecision_comp_green
      (cmp99ActiveGaugeRegionReindex e Omega)
      (finitePiLpTypedKernelReindex e e K) hc hK'
  change finitePiLpTypedKernelReindex E E G = G'
  apply ContinuousLinearMap.ext
  intro phi
  apply isCoerciveCLM_injective A' hc hA'
  have hleft := congrArg
    (fun T : ActiveGaugeZeroCochain
        (cmp99ActiveGaugeRegionReindex e Omega) g →L[ℝ]
        ActiveGaugeZeroCochain (cmp99ActiveGaugeRegionReindex e Omega) g =>
      T phi) htransport
  have hright := congrArg
    (fun T : ActiveGaugeZeroCochain
        (cmp99ActiveGaugeRegionReindex e Omega) g →L[ℝ]
        ActiveGaugeZeroCochain (cmp99ActiveGaugeRegionReindex e Omega) g =>
      T phi) hcanonical
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply]
    using hleft.trans hright.symm

end

end YangMills.RG
