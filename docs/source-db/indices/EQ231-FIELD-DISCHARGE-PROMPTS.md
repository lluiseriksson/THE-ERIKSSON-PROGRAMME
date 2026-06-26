# Eq. (2.31) field-discharge prompts — Batch 004

## Prompt A — bond first-coordinate in gapCubes

You are assisting `lluiseriksson/THE-ERIKSSON-PROGRAMME` after HEAD `8b98c43`.

Do not add downstream wrappers. Prove or source-shape the premise:

```lean
∀ Z D P,
  sourceAdmissible Z D P →
    ∀ b : Cube × Fin 4,
      b ∈ P → b.1 ∈ gapCubes Z D
```

Use source keys:

```text
cmp116.eq231.p-family-carrier-source-target
cmp109.bond-convention.positive-oriented
cmp109.b0-corridor-bond
crosswalk.eq231.p-family-source-dictionary-route
```

Deliverables:

1. Exact source sentence proving base-cube ownership, or the exact missing lemma.
2. Proposed Lean theorem name: `cmp116Eq231_bond_fst_mem_gapCubes_of_sourceAdmissible`.
3. Proof that `source_subset_gapCarrier` then follows by `cmp116Eq231_source_subset_gapCarrier_of_bond_fst_mem_gapCubes`.
4. State whether the factor is 4 or must be 8 if only incidence is known.
5. Do not claim `mem_iff_source` or `admissible_iff_source` unless both directions are sourced.

## Prompt B — membership iff

Extract the source-native theorem:

```lean
P ∈ PIndex Z D ↔ sourceAdmissible Z D P
```

Then connect it to the filtered Lean family only after admissible is source-defined, not vacuous.

## Prompt C — admissible iff without vacuity

Define `admissible` by source clauses: interior of `Z0`, no `dZ0` intersection, smallest localization domain containing `Y0` and `P`, and any additional CMP116 clauses.  Do not define it as `decide (P ∈ PIndex Z D)`.
