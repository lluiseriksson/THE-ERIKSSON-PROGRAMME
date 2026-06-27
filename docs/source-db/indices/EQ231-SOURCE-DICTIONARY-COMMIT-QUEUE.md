# Eq. (2.31) source dictionary commit queue after HEAD 1fed14e

1. **Prove/source-shape bond ownership.**
   - Target: `CMP116Eq231PositiveTailOwnershipSource.positive_tail_in_gap`.
   - Consumed by: `cmp116Eq231_sourcePIndexMemIff_of_positiveTailOwnership`,
     `CMP116Eq231PBondBoundary.of_positiveTailOwnership`,
     `CMP116Lemma3PStageSourceScaleBoundary.of_eq231_positiveTailOwnership`, and
     `CMP116Lemma3WeightedPostPScaleSourceAssumptions.of_eq231_positiveTailOwnership`.
   - Removes: the raw carrier-containment route once `mem_iff_source` and
     `admissible_iff_source` are also available.
   - Current source status: CMP116 page 12 supplies the interior/no-boundary
     split; the first-coordinate/base-cube dictionary remains pending.

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
