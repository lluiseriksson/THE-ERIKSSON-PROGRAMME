import YangMills.RG.BalabanCMP99SourceActiveRegionFullCompanionAmbientPrecision

/-!
SCRATCH / NOT SHIPPED.  Generic active-region transport needed after the C6d
ambient Green is specialized to the source-separated Step-7b carrier.  No
compiler or axiom-oracle verdict is claimed.
-/

namespace YangMills.RG

open YangMills

noncomputable section

variable {d N N' : ℕ} [NeZero N] [NeZero N']

/-- Reindexing a square finite counting-Hilbert kernel forward and then
through the explicit inverse recovers the original kernel.  Carrier
cancellation is kept as a theorem because the two presentations are not
definitionally equal. -/
theorem finitePiLpTypedKernelReindex_symm_reindex
    {ι ι' g : Type*} [Fintype ι] [Fintype ι']
    [NormedAddCommGroup g] [NormedSpace ℝ g]
    (e : ι ≃ ι')
    (T : FinitePiLpField ι g →L[ℝ] FinitePiLpField ι g) :
    finitePiLpTypedKernelReindex e.symm e.symm
        (finitePiLpTypedKernelReindex e e T) = T := by
  apply ContinuousLinearMap.ext
  intro phi
  apply PiLp.ext
  intro x
  have hcancel :
      (LinearIsometryEquiv.piLpCongrLeft 2 ℝ g e.symm)
          ((LinearIsometryEquiv.piLpCongrLeft 2 ℝ g e) phi) = phi := by
    simpa only [LinearIsometryEquiv.piLpCongrLeft_symm] using
      (LinearIsometryEquiv.piLpCongrLeft 2 ℝ g e).symm_apply_apply phi
  simp [finitePiLpTypedKernelReindex,
    LinearIsometryEquiv.piLpCongrLeft_apply, Equiv.piCongrLeft', hcancel]

/-- Transport an active region through one explicit equivalence of ambient
finite periodic carriers. -/
noncomputable def cmp99ActiveGaugeRegionReindex
    (e : FinBox d N ≃ FinBox d N') (Omega : ActiveGaugeRegion d N) :
    ActiveGaugeRegion d N' :=
  ⟨Omega.sites.map e.toEmbedding⟩

/-- Membership in the transported region is exactly membership of the
inverse image in the original region. -/
theorem mem_cmp99ActiveGaugeRegionReindex_iff
    (e : FinBox d N ≃ FinBox d N') (Omega : ActiveGaugeRegion d N)
    (y : FinBox d N') :
    y ∈ (cmp99ActiveGaugeRegionReindex e Omega).sites ↔
      e.symm y ∈ Omega.sites := by
  simp [cmp99ActiveGaugeRegionReindex]

/-- The ambient equivalence restricts to a named equivalence of the two
localized site subtypes. -/
noncomputable def cmp99ActiveGaugeRegionSiteReindexEquiv
    (e : FinBox d N ≃ FinBox d N') (Omega : ActiveGaugeRegion d N) :
    ActiveGaugeRegion.Site Omega ≃
      ActiveGaugeRegion.Site (cmp99ActiveGaugeRegionReindex e Omega) :=
  e.subtypeEquiv fun x => by
    simp [cmp99ActiveGaugeRegionReindex]

/-- Transporting a region forward and then back recovers it exactly. -/
theorem cmp99ActiveGaugeRegionReindex_symm_reindex_eq
    (e : FinBox d N ≃ FinBox d N') (Omega : ActiveGaugeRegion d N) :
    cmp99ActiveGaugeRegionReindex e.symm
        (cmp99ActiveGaugeRegionReindex e Omega) = Omega := by
  rcases Omega with ⟨sites⟩
  apply congrArg ActiveGaugeRegion.mk
  ext x
  simp [cmp99ActiveGaugeRegionReindex]

/-- Ambient zero-field coordinate transport through the same carrier
equivalence. -/
noncomputable def cmp99GaugeZeroCochainReindex
    {g : Type*} [NormedAddCommGroup g] [InnerProductSpace ℝ g]
    [FiniteDimensional ℝ g]
    (e : FinBox d N ≃ FinBox d N') :
    GaugeZeroCochain d N g ≃L[ℝ] GaugeZeroCochain d N' g :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℝ g e).toContinuousLinearEquiv

/-- Localized zero-field coordinate transport through the restricted site
equivalence. -/
noncomputable def cmp99ActiveGaugeZeroCochainReindex
    {g : Type*} [NormedAddCommGroup g] [InnerProductSpace ℝ g]
    [FiniteDimensional ℝ g]
    (e : FinBox d N ≃ FinBox d N') (Omega : ActiveGaugeRegion d N) :
    ActiveGaugeZeroCochain Omega g ≃L[ℝ]
      ActiveGaugeZeroCochain (cmp99ActiveGaugeRegionReindex e Omega) g :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℝ g
    (cmp99ActiveGaugeRegionSiteReindexEquiv e Omega)).toContinuousLinearEquiv

/-- Extension by zero commutes with explicit transport of the ambient and
localized carriers. -/
theorem cmp99GaugeZeroCochainReindex_extendZero
    {g : Type*} [NormedAddCommGroup g] [InnerProductSpace ℝ g]
    [FiniteDimensional ℝ g]
    (e : FinBox d N ≃ FinBox d N') (Omega : ActiveGaugeRegion d N)
    (phi : ActiveGaugeZeroCochain Omega g) :
    cmp99GaugeZeroCochainReindex e (extendZeroZeroCLM Omega phi) =
      extendZeroZeroCLM (cmp99ActiveGaugeRegionReindex e Omega)
        (cmp99ActiveGaugeZeroCochainReindex e Omega phi) := by
  apply PiLp.ext
  intro y
  change (if hx : e.symm y ∈ Omega.sites then phi ⟨e.symm y, hx⟩ else 0) =
    (if hy : y ∈ (cmp99ActiveGaugeRegionReindex e Omega).sites then
      cmp99ActiveGaugeZeroCochainReindex e Omega phi ⟨y, hy⟩ else 0)
  by_cases hy : y ∈ (cmp99ActiveGaugeRegionReindex e Omega).sites
  · have hx : e.symm y ∈ Omega.sites :=
      (mem_cmp99ActiveGaugeRegionReindex_iff e Omega y).mp hy
    rw [dif_pos hx, dif_pos hy]
    simp [cmp99ActiveGaugeZeroCochainReindex,
      LinearIsometryEquiv.piLpCongrLeft_apply, Equiv.piCongrLeft',
      cmp99ActiveGaugeRegionSiteReindexEquiv]
  · have hx : e.symm y ∉ Omega.sites := by
      intro hx
      exact hy ((mem_cmp99ActiveGaugeRegionReindex_iff e Omega y).mpr hx)
    rw [dif_neg hx, dif_neg hy]

/-- Restriction commutes with explicit transport of the ambient and
localized carriers. -/
theorem cmp99ActiveGaugeZeroCochainReindex_restrictZero
    {g : Type*} [NormedAddCommGroup g] [InnerProductSpace ℝ g]
    [FiniteDimensional ℝ g]
    (e : FinBox d N ≃ FinBox d N') (Omega : ActiveGaugeRegion d N)
    (phi : GaugeZeroCochain d N g) :
    cmp99ActiveGaugeZeroCochainReindex e Omega (restrictZeroCLM Omega phi) =
      restrictZeroCLM (cmp99ActiveGaugeRegionReindex e Omega)
        (cmp99GaugeZeroCochainReindex e phi) := by
  apply PiLp.ext
  intro y
  simp [cmp99ActiveGaugeZeroCochainReindex,
    cmp99GaugeZeroCochainReindex,
    LinearIsometryEquiv.piLpCongrLeft_apply,
    Equiv.piCongrLeft', cmp99ActiveGaugeRegionSiteReindexEquiv,
    restrictZeroCLM]

/-- The inverse ambient transport of a zero extension is the zero extension
of the inverse localized transport. -/
theorem cmp99GaugeZeroCochainReindex_symm_extendZero
    {g : Type*} [NormedAddCommGroup g] [InnerProductSpace ℝ g]
    [FiniteDimensional ℝ g]
    (e : FinBox d N ≃ FinBox d N') (Omega : ActiveGaugeRegion d N)
    (phi : ActiveGaugeZeroCochain
      (cmp99ActiveGaugeRegionReindex e Omega) g) :
    (cmp99GaugeZeroCochainReindex e).symm
        (extendZeroZeroCLM (cmp99ActiveGaugeRegionReindex e Omega) phi) =
      extendZeroZeroCLM Omega
        ((cmp99ActiveGaugeZeroCochainReindex e Omega).symm phi) := by
  have h := cmp99GaugeZeroCochainReindex_extendZero e Omega
    ((cmp99ActiveGaugeZeroCochainReindex e Omega).symm phi)
  rw [(cmp99ActiveGaugeZeroCochainReindex e Omega).apply_symm_apply] at h
  have hs := congrArg (cmp99GaugeZeroCochainReindex e).symm h
  have hs' :
      extendZeroZeroCLM Omega
          ((cmp99ActiveGaugeZeroCochainReindex e Omega).symm phi) =
        (cmp99GaugeZeroCochainReindex e).symm
          (extendZeroZeroCLM (cmp99ActiveGaugeRegionReindex e Omega) phi) := by
    simpa only [(cmp99GaugeZeroCochainReindex e).symm_apply_apply] using hs
  exact hs'.symm

/-- Reindexing the ambient precision and the localized carrier commutes
exactly with Dirichlet compression.  This is the carrier dictionary needed
before a C6d Green can be read on the source-separated Step-7b box. -/
theorem finitePiLpTypedKernelReindex_sourceAmbientDirichletPrecision
    {g : Type*} [NormedAddCommGroup g] [InnerProductSpace ℝ g]
    [FiniteDimensional ℝ g]
    (e : FinBox d N ≃ FinBox d N') (Omega : ActiveGaugeRegion d N)
    (K : GaugeZeroCochain d N g →L[ℝ] GaugeZeroCochain d N g) :
    finitePiLpTypedKernelReindex
        (cmp99ActiveGaugeRegionSiteReindexEquiv e Omega)
        (cmp99ActiveGaugeRegionSiteReindexEquiv e Omega)
        (cmp99SourceAmbientDirichletPrecision Omega K) =
      cmp99SourceAmbientDirichletPrecision
        (cmp99ActiveGaugeRegionReindex e Omega)
        (finitePiLpTypedKernelReindex e e K) := by
  apply ContinuousLinearMap.ext
  intro phi
  simp only [finitePiLpTypedKernelReindex,
    cmp99SourceAmbientDirichletPrecision,
    ContinuousLinearMap.comp_apply]
  have hrestrict := cmp99ActiveGaugeZeroCochainReindex_restrictZero e Omega
    (K (extendZeroZeroCLM Omega
      ((cmp99ActiveGaugeZeroCochainReindex e Omega).symm phi)))
  have hext := cmp99GaugeZeroCochainReindex_symm_extendZero e Omega phi
  calc
    _ = restrictZeroCLM (cmp99ActiveGaugeRegionReindex e Omega)
        (cmp99GaugeZeroCochainReindex e
          (K (extendZeroZeroCLM Omega
            ((cmp99ActiveGaugeZeroCochainReindex e Omega).symm phi)))) := by
      simpa only [cmp99ActiveGaugeZeroCochainReindex,
        cmp99GaugeZeroCochainReindex,
        ← LinearIsometryEquiv.toContinuousLinearEquiv_symm,
        LinearIsometryEquiv.piLpCongrLeft_symm] using hrestrict
    _ = _ := by
      rw [← hext]
      simp only [cmp99GaugeZeroCochainReindex,
        ← LinearIsometryEquiv.toContinuousLinearEquiv_symm,
        LinearIsometryEquiv.piLpCongrLeft_symm]
      rfl

/-- Pulling the transported Dirichlet compression back through the restricted
site equivalence recovers the original compression.  This is the exact
inverse-orientation statement consumed by the source-separated carrier. -/
theorem finitePiLpTypedKernelReindex_symm_sourceAmbientDirichletPrecision
    {g : Type*} [NormedAddCommGroup g] [InnerProductSpace ℝ g]
    [FiniteDimensional ℝ g]
    (e : FinBox d N ≃ FinBox d N') (Omega : ActiveGaugeRegion d N)
    (K : GaugeZeroCochain d N g →L[ℝ] GaugeZeroCochain d N g) :
    finitePiLpTypedKernelReindex
        (cmp99ActiveGaugeRegionSiteReindexEquiv e Omega).symm
        (cmp99ActiveGaugeRegionSiteReindexEquiv e Omega).symm
        (cmp99SourceAmbientDirichletPrecision
          (cmp99ActiveGaugeRegionReindex e Omega)
          (finitePiLpTypedKernelReindex e e K)) =
      cmp99SourceAmbientDirichletPrecision Omega K := by
  rw [← finitePiLpTypedKernelReindex_sourceAmbientDirichletPrecision
    e Omega K]
  exact finitePiLpTypedKernelReindex_symm_reindex
    (cmp99ActiveGaugeRegionSiteReindexEquiv e Omega)
    (cmp99SourceAmbientDirichletPrecision Omega K)

end

end YangMills.RG
