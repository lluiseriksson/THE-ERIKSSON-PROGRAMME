# Eq. (2.31) source dictionary commit queue after HEAD 8b98c43

1. **Prove/source-shape bond ownership.**
   - Target: `cmp116Eq231_bond_fst_mem_gapCubes_of_sourceAdmissible`.
   - Consumed by: `cmp116Eq231_source_subset_gapCarrier_of_bond_fst_mem_gapCubes`.
   - Removes: `source_subset_gapCarrier` field once sourceAdmissible is available.

2. **Prove `mem_iff_source`.**
   - Target: source P-family membership iff.
   - Removes: the `PIndex` side of the filtered family dictionary.

3. **Prove `admissible_iff_source` without vacuity.**
   - Target: source clauses ↔ Lean Bool admissible.
   - Removes: opaque/ad-hoc admissibility field.

4. **Prove pointwise P-residual majorization.**
   - Target: analytic Eq. (2.31) residual-to-geometry bound.
   - Separate from dictionary work.

5. **Only after 1–4:** connect to weighted post-P and raw-source M3 routes.  Existing consumers already exist; avoid adding more.
