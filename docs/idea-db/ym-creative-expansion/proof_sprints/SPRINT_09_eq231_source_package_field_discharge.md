# Sprint 09 — Eq. (2.31) source package field discharge

## Target

Remove exactly one field from:

```lean
CMP116Eq231BalabanPFamilySourcePackage
```

Fields:

```text
mem_iff_source
source_subset_gapCarrier
admissible_iff_source
```

## Recommended field

Start with `source_subset_gapCarrier`, via the narrower theorem:

```lean
cmp116Eq231_source_subset_gapCarrier_of_bond_fst_mem_gapCubes
```

Source-shaped premise:

```text
sourceAdmissible Z D P -> forall b in P, b.1 in gapCubes Z D
```

## Acceptance

A successful patch either proves this premise from source-backed definitions or
records the exact missing source theorem name and source window. It must not add
a new downstream constructor.
