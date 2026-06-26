# CMP116 Eq. (2.31) source-package live fields — Batch 004

Purpose: align the source database with the post-`8b98c43` route.  The repository now has a conditional theorem
`cmp116Eq231_source_subset_gapCarrier_of_bond_fst_mem_gapCubes`, so the next progress must prove one of the remaining source-native fields, not add downstream wrappers.

## Live fields

| Field | Best next theorem | Source keys | Removes | Status |
|---|---|---|---|---|
| `source_subset_gapCarrier` | `bond_fst_mem_gapCubes` then apply `cmp116Eq231_source_subset_gapCarrier_of_bond_fst_mem_gapCubes` | `cmp116.eq231.p-family-carrier-source-target`, `cmp109.bond-convention.positive-oriented` | carrier containment premise | narrowed, still source-pending |
| `mem_iff_source` | `P ∈ PIndex ↔ sourceAdmissible Z D P` | `cmp116.eq231.p-family-carrier-source-target` | filtered PIndex dictionary | open |
| `admissible_iff_source` | `admissible Z D P = true ↔ source clauses` | CMP116 page-12/page-18/19 P-family text | anti-vacuity for admissible | open |
| pointwise P residual | `pResidualWeight ≤ constant * pGeometryWeight` | CMP116 Eq. (2.31) analytic window | P-stage analytic bound | separate analytic blocker |

## Immediate rule

A commit is useful only if it removes one of the live fields above or proves a source-shaped premise that feeds an existing remover.  Another theorem forwarding `hPIndex`, `hPcarrier` or `CMP116Eq231PBondBoundary` without shrinking assumptions is cosmetic.

## Smallest high-payoff target

```lean
∀ Z D P,
  sourceAdmissible Z D P →
    ∀ b : Cube × Fin 4,
      b ∈ P → b.1 ∈ gapCubes Z D
```

This is exactly the premise consumed by:

```lean
cmp116Eq231_source_subset_gapCarrier_of_bond_fst_mem_gapCubes
```

It is smaller than the full membership iff and should be attempted first if CMP116/CMP109 only provide carrier/orientation information.
