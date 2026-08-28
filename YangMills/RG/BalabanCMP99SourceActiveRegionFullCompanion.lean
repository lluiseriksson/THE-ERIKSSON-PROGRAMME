import YangMills.RG.BalabanCMP99SourceGeneratedMassTransition

/-!
PRE-VALIDATION: source present; `.olean` not yet materialized and the result
has not yet been verified by the compiler or axiom oracle.

# Canonical full companion of an arbitrary source-region chain

Every typed C6d region chain is embedded, scale by scale, in a chain whose
active region is the full carrier at every level.  Both the companion and the
nestedness witness are constructed recursively; neither is caller data.

This is geometric infrastructure for transporting the generated counting
mass from the physical ambient tower to the localized C6d tower.  It does not
construct a precision, Green, Eq. (3.42) bound, or terminal field.
-/

namespace YangMills.RG

noncomputable section

variable {d M N : ℕ} [NeZero M]

/-- The full active region on one finite periodic carrier. -/
def cmp99SourceFullActiveRegion (d N : ℕ) : ActiveGaugeRegion d N :=
  ⟨Finset.univ⟩

/-- The full region is block saturated at every nondegenerate blocking
step. -/
theorem cmp99SourceFullActiveRegion_blockSaturated
    {N' : ℕ} [NeZero N'] :
    (cmp99SourceFullActiveRegion d (M * N')).BlockSaturated := by
  intro x _ z _
  exact Finset.mem_univ z

/-- Coarsening a full region gives the full coarse region exactly. -/
theorem cmp99ActiveCoarseRegion_sourceFull_eq
    {N' : ℕ} [NeZero N'] :
    cmp99ActiveCoarseRegion (M := M) (N' := N')
        (cmp99SourceFullActiveRegion d (M * N')) =
      cmp99SourceFullActiveRegion d N' := by
  congr 1
  ext y
  simp [cmp99SourceFullActiveRegion]

/-- A full companion together with the scale-by-scale nesting theorem. -/
structure CMP99SourceActiveRegionFullCompanion
    {Omega : ActiveGaugeRegion d N} {depth : ℕ}
    (regions : CMP99SourceActiveRegionChain d M N Omega depth) where
  large : CMP99SourceActiveRegionChain d M N
    (cmp99SourceFullActiveRegion d N) depth
  nested : CMP99SourceNestedRegionChains d M regions large

/-- Construct the full companion recursively from the supplied typed chain.
The only inclusion used at each scale is membership in `Finset.univ`. -/
noncomputable def cmp99SourceActiveRegionFullCompanion
    {Omega : ActiveGaugeRegion d N} {depth : ℕ}
    (regions : CMP99SourceActiveRegionChain d M N Omega depth) :
    CMP99SourceActiveRegionFullCompanion regions := by
  induction regions with
  | stop Omega =>
      refine ⟨CMP99SourceActiveRegionChain.stop
          (cmp99SourceFullActiveRegion d _), ?_⟩
      exact .stop Omega (cmp99SourceFullActiveRegion d _) (by
        intro x _
        exact Finset.mem_univ x)
  | @step N' depth _ Omega hOmega tail ih =>
      let OmegaFull := cmp99SourceFullActiveRegion d (M * N')
      have hFull : OmegaFull.BlockSaturated :=
        cmp99SourceFullActiveRegion_blockSaturated (d := d) (M := M)
      have hCoarse : cmp99ActiveCoarseRegion (M := M) (N' := N') OmegaFull =
          cmp99SourceFullActiveRegion d N' := by
        exact cmp99ActiveCoarseRegion_sourceFull_eq (d := d) (M := M)
      let tailLarge : CMP99SourceActiveRegionChain d M N'
          (cmp99ActiveCoarseRegion (M := M) (N' := N') OmegaFull) depth :=
        hCoarse.symm ▸ ih.large
      have hTail : CMP99SourceNestedRegionChains d M tail tailLarge := by
        exact CMP99SourceNestedRegionChains.cast_regions rfl hCoarse.symm
          ih.nested
      refine ⟨CMP99SourceActiveRegionChain.step OmegaFull hFull tailLarge, ?_⟩
      exact .step Omega OmegaFull hOmega hFull (by
        intro x _
        exact Finset.mem_univ x) tail tailLarge hTail

end

end YangMills.RG
