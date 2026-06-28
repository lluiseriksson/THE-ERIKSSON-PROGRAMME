# Eq. (2.31) source dictionary commit queue at public main 0d87ecc6

1. **Prove or source-shape the corrected endpoint/base dictionary.**
   - Target:
     `CMP116Eq231Y0cStarInteriorBoundaryToGapSource.positive_tail_of_y0cStar_interior_boundary_in_gap`.
   - Consumed by: `cmp116Eq231_sourcePIndexMemIff_of_positiveTailOwnership`,
     `CMP116Eq231PBondBoundary.of_positiveTailOwnership`,
     `CMP116Lemma3PStageSourceScaleBoundary.of_eq231_positiveTailOwnership`, and
     `CMP116Lemma3WeightedPostPScaleSourceAssumptions.of_eq231_positiveTailOwnership`.
   - Removes: the raw carrier-containment route once `mem_iff_source` and
     `admissible_iff_source` are also available.
   - Current source status: CMP116 page 12 supplies the interior/no-boundary
     split, but the active source-lock must also keep
     `bondInY0cStar`.  The first-coordinate/base-cube dictionary remains
     pending.
   - Guardrail status: `exists_fullCarrierAdmissibility_without_y0cStarInteriorBoundaryToGapSource`
     and `exists_fullCarrierAdmissibility_without_positiveTailOwnershipSource`
     show that the page-12 split alone does not imply this target.

2. **Prove `mem_iff_source`.**
   - Target: source P-family membership iff.
   - Removes: the `PIndex` side of the filtered family dictionary.

3. **Prove `admissible_iff_source` without vacuity.**
   - Target: source clauses ↔ Lean Bool admissible.
   - Removes: opaque/ad-hoc admissibility field.

4. **Prove pointwise P-residual majorization.**
   - Target: analytic Eq. (2.31) residual-to-geometry bound.
   - Separate from dictionary work.

5. **Only after 1–4:** connect to weighted post-P and raw-source M3 routes.
   Existing consumers already exist; avoid adding more.
