import YangMills.RG.BalabanCMP99Eq360C6dSourceSeparatedAmbientGreen
import YangMills.RG.BalabanCMP99SourceActiveRegionFullCompanionAmbientPrecision

/-!
PRE-VALIDATION: source present; its `.olean` is not yet materialized and the result is not compiler-verified.

Named metric transport for the two exact reindexing legs consumed by the
C6d Green-decay producer.
-/

namespace YangMills.RG

open YangMills

noncomputable section

/-- The literal full-active-region equivalence preserves periodic distance.
This is definitionally simple but named so no consumer relies on the word
`reindex`. -/
theorem finBoxDist_cmp99SourceFullActiveRegionSiteEquiv
    (d N : ℕ)
    (x y : ActiveGaugeRegion.Site (cmp99SourceFullActiveRegion d N)) :
    finBoxDist (cmp99SourceFullActiveRegionSiteEquiv d N x)
        (cmp99SourceFullActiveRegionSiteEquiv d N y) =
      finBoxDist x.1 y.1 := by
  rfl

/-- The generated one-block active-site equivalence is only a carrier cast,
so it preserves the periodic metric exactly. -/
theorem finBoxDist_cmp99SourceSeparatedGeneratedPhysicalStep7bActiveSiteEquiv
    (L K Q depth : ℕ) [NeZero L] [NeZero K] [NeZero Q]
    (x y : ActiveGaugeRegion.Site
      (cmp99IteratedLiftActiveRegion (M := L)
        (cmp99SourceSeparatedGeneratedPhysicalFullCoarseRegion K Q)
        (depth + 1))) :
    finBoxDist
        (cmp99SourceSeparatedGeneratedPhysicalStep7bActiveSiteEquiv
          L K Q depth x)
        (cmp99SourceSeparatedGeneratedPhysicalStep7bActiveSiteEquiv
          L K Q depth y) =
      finBoxDist x.1 y.1 := by
  let hsize := cmp99RegionalLatticeSize_eq_pow_mul
    L (2 * (K * Q)) (depth + 1)
  change finBoxDist (hsize ▸ x.1) (hsize ▸ y.1) = finBoxDist x.1 y.1
  exact finBoxDist_cast_size hsize x.1 y.1

/-- The exact source-separated Step-7b carrier equivalence preserves the
periodic metric.  Both the generated one-block cast and separated carrier
cast are cited explicitly. -/
theorem finBoxDist_cmp99Eq360C6dSourceSeparatedAmbientSiteEquiv
    (L K Q depth : ℕ) [NeZero L] [NeZero K] [NeZero Q]
    (x y : FinBox 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q))) :
    finBoxDist
        (cmp99Eq360C6dSourceSeparatedAmbientSiteEquiv
          (L := L) (K := K) (Q := Q) (depth := depth) x)
        (cmp99Eq360C6dSourceSeparatedAmbientSiteEquiv
          (L := L) (K := K) (Q := Q) (depth := depth) y) =
      finBoxDist x y := by
  let eFull :=
    cmp99SourceSeparatedGeneratedPhysicalFullSiteEquiv L K Q depth
  let eActive :=
    cmp99SourceSeparatedGeneratedPhysicalStep7bActiveSiteEquiv L K Q depth
  have hcast :
      finBoxDist (eActive (eFull.symm x)) (eActive (eFull.symm y)) =
        finBoxDist (eFull.symm x).1 (eFull.symm y).1 := by
    exact
      finBoxDist_cmp99SourceSeparatedGeneratedPhysicalStep7bActiveSiteEquiv
        L K Q depth (eFull.symm x) (eFull.symm y)
  have hfull :=
    finBoxDist_cmp99SourceSeparatedGeneratedPhysicalFullSiteEquiv_symm
      L K Q depth x y
  change finBoxDist (eActive (eFull.symm x)) (eActive (eFull.symm y)) =
    finBoxDist x y
  rw [hcast, hfull]

end

end YangMills.RG
