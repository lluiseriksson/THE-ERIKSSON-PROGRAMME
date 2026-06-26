# Sprint 01 — Eq. (2.31) source membership iff

Objective: prove or source-shape the exact `hmem` premise consumed by `CMP116Eq231PBondBoundary.of_sourcePIndexMemIff`.

Lean target:
```lean
cmp116Eq231_balabanPFamily_sourcePIndexMemIff
```

Minimal honest result:
- a record with fields `mem_iff_source`, `source_subset_gapCarrier`, `admissible_iff_source`;
- no new consumers;
- no vacuous admissibility predicate.

Steps:
1. Identify source P objects and their bond orientation.
2. Prove carrier inclusion into `gapCubes × Fin 4`.
3. Define admissibility as a named source predicate, not `fun _ => true` unless source genuinely says all subsets qualify.
4. Prove iff or split into one-way theorem plus explicit remaining blocker.
