import YangMills.RG.BalabanCMP99SourceSeparatedGeneratedFlatPhysicalStep7bCarrier
import YangMills.RG.BalabanCMP99Eq389SourceLocalizationOwner

/-!
# BalabanCMP99SourceFlowPhysicalOwnerDictionary

Cold-verified and .olean materialized at source b2d5df8ad on 2026-09-05.
Downloaded evidence independently verified; see ledger Addendum 1122.
This selective seal changes provenance comments only, not the mathematics.
Its draft was checked at 6f20ead457a528c2e5df6cc5fa2318fe43dbeeda; see ledger 1120.
Only the explicit public-name map and audit placement are changed.

Exact physical/source-localization site and owner equalities, and the cardinality of one owner fibre. No count of all owners, outer-norm transport or regional inverse.
No window-15 attainment or terminal field is claimed; 20/41, TermSource=0.
-/

namespace YangMills.RG

open YangMills
noncomputable section

private theorem physicalOwner_sizeTransport_val
    {d A B : ℕ} (h : A = B) (x : FinBox d A) (i : Fin d) :
    ((h ▸ x : FinBox d B) i).val = (x i).val := by
  cases h
  rfl

private theorem physicalOwner_equivCast_val
    {d A B : ℕ} (h : A = B) (x : FinBox d A) (i : Fin d) :
    ((Equiv.cast (congrArg (FinBox d) h) x) i).val = (x i).val := by
  cases h
  rfl

variable {L K Q : ℕ} [NeZero L] [NeZero K] [NeZero Q]

private instance physicalOwnerDraft_blockNeZero (depth : ℕ) :
    NeZero (L ^ (depth + 1)) :=
  ⟨(pow_pos (NeZero.pos L) (depth + 1)).ne'⟩

/-- The generated ambient-to-Step7b coordinate map is exactly the source
localization cast; it does not secretly permute fine coordinates. -/
theorem cmp99PhysicalStep7bSiteEquiv_eq_sourceLocalization
    (depth : ℕ) :
    cmp99SourceSeparatedGeneratedPhysicalStep7bSiteEquiv L K Q depth =
      cmp99Eq389SourceLocalizationSiteEquiv L K Q depth := by
  apply Equiv.ext
  intro x
  funext i
  apply Fin.ext
  let hsize := cmp99RegionalLatticeSize_sourceSeparatedLargeBlockCarrier L K Q depth
  have hleft :
      ((cmp99SourceSeparatedGeneratedPhysicalStep7bSiteEquiv L K Q depth x) i).val =
        (x i).val := by
    change ((cmp99GeneratedFineBoxOneBlockEquiv (d := 4) L (2 * (K * Q))
      (depth + 1) (hsize.symm ▸ x)) i).val = (x i).val
    rw [cmp99GeneratedFineBoxOneBlockEquiv_apply_val]
    exact physicalOwner_sizeTransport_val hsize.symm x i
  have hright :
      ((cmp99Eq389SourceLocalizationSiteEquiv L K Q depth x) i).val =
        (x i).val :=
    physicalOwner_equivCast_val
      (cmp99SourceSeparatedCarrier_eq_sourceLocalizationCarrier L K Q depth) x i
  exact hleft.trans hright.symm

/-- The owner used in the physical point-source bound is literally the
owner used by the source-localized action consumer. -/
theorem cmp99PhysicalStep7b_blockSite_eq_sourceLocalizationOwner
    (depth : ℕ)
    (x : FinBox 4 (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q))) :
    blockSite (L ^ (depth + 1)) (2 * (K * Q))
        (cmp99SourceSeparatedGeneratedPhysicalStep7bSiteEquiv L K Q depth x) =
      cmp99Eq389SourceLocalizationOwner L K Q depth x := by
  rw [cmp99PhysicalStep7bSiteEquiv_eq_sourceLocalization]
  rfl

open scoped Classical in
/-- Full ambient source-localization fibres have exactly R^4 sites.
This transports the existing blockOf_card theorem, not an ambient-volume
estimate or a new count of owners. -/
theorem card_cmp99SourceLocalizationOwner_fibre
    (depth : ℕ) (owner : FinBox 4 (2 * (K * Q))) :
    (Finset.univ.filter (fun x : FinBox 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)) =>
        cmp99Eq389SourceLocalizationOwner L K Q depth x = owner)).card =
      (L ^ (depth + 1)) ^ 4 := by
  classical
  let e := cmp99Eq389SourceLocalizationSiteEquiv L K Q depth
  rw [← blockOf_card (L ^ (depth + 1)) (2 * (K * Q)) owner]
  apply Finset.card_bij (fun x _ => e x)
  · intro x hx
    rw [mem_blockOf]
    exact (Finset.mem_filter.mp hx).2
  · intro x _ y _ hxy
    exact e.injective hxy
  · intro y hy
    refine ⟨e.symm y, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩,
      e.apply_symm_apply y⟩
    change blockSite (L ^ (depth + 1)) (2 * (K * Q)) (e (e.symm y)) = owner
    rw [e.apply_symm_apply]
    exact (mem_blockOf (L ^ (depth + 1)) (2 * (K * Q)) owner y).mp hy


end
end YangMills.RG
