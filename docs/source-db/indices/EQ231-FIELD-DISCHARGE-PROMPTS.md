# Eq. (2.31) field-discharge prompts — Batch 004

## Prompt A — bond first-coordinate in gapCubes

You are assisting `lluiseriksson/THE-ERIKSSON-PROGRAMME` after HEAD `1fed14e`.

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
2. Preferred Lean target: `CMP116Eq231PositiveTailOwnershipSource.positive_tail_in_gap`.
3. Existing downstream routes that should consume it:
   `cmp116Eq231_sourcePIndexMemIff_of_positiveTailOwnership`,
   `CMP116Eq231PBondBoundary.of_positiveTailOwnership`,
   `CMP116Lemma3PStageSourceScaleBoundary.of_eq231_positiveTailOwnership`, and
   `CMP116Lemma3WeightedPostPScaleSourceAssumptions.of_eq231_positiveTailOwnership`.
4. State whether the factor is 4 or must be 8 if only incidence is known.
5. Do not claim `mem_iff_source` or `admissible_iff_source` unless both directions are sourced.

Current source-search result: CMP116 page 12 proves the interior/no-`dZ0`
source split, and pages 18-19 discuss `P` bonds connecting cubes in `Z0 \ Y0`,
but the exact first-coordinate/base-cube dictionary is still not source-closed.

## Prompt B — membership iff

Extract the source-native theorem:

```lean
P ∈ PIndex Z D ↔ sourceAdmissible Z D P
```

Then connect it to the filtered Lean family only after admissible is source-defined, not vacuous.

## Prompt C — admissible iff without vacuity

Define `admissible` by source clauses: interior of `Z0`, no `dZ0` intersection, smallest localization domain containing `Y0` and `P`, and any additional CMP116 clauses.  Do not define it as `decide (P ∈ PIndex Z D)`.
