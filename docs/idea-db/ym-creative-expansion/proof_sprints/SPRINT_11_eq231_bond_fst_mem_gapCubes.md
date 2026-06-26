# Sprint 11 — Eq. (2.31) bond first-coordinate membership

## Exact target

```lean
cmp116Eq231_bond_fst_mem_gapCubes_of_sourceAdmissible
```

Target shape:

```text
∀ Z D P,
  sourceAdmissible Z D P ->
    ∀ b : Cube × Fin 4, b ∈ P -> b.1 ∈ gapCubes Z D
```

## Source windows

- `cmp116.eq231.p-family-carrier-source-target`
- `cmp109.bond-convention.positive-oriented`
- `cmp109.b0-corridor-bond`
- `crosswalk.eq231.p-family-source-dictionary-route` for navigation only

## Anti-errors

- CMP109 gives orientation convention, not the CMP116 carrier theorem by itself.
- Factor 4 requires positive-direction uniqueness; unoriented bonds can double.
- Do not use `|P|` lower bound as carrier membership.
