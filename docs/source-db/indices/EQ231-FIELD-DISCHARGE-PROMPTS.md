# Eq. (2.31) field-discharge prompts — Batch 004

## Prompt A — bond first-coordinate in gapCubes

You are assisting `lluiseriksson/THE-ERIKSSON-PROGRAMME` after HEAD `b85079a`.

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

Current visual recheck after HEAD `4432292`: local renders
`cmp116-source-12-eq25-28.png`, `cmp116-source-18.png`,
`cmp116-source-19.png`, and `cmp109-source-19-b0-corridor-19.png` confirm the
same boundary.  Page 12 gives `P ⊂ Y0^{c,*}`, smallest `Z0` containing `Y0`
and `P`, and interior/no-`dZ0`; page 18 gives the `|P|` lower-bound rationale
that one bond in `P` may connect two cubes in `Z0 \ Y0`; page 19 continues the
sum estimate; CMP109 page 267 defines `b0(c)`.  None of these renders proves
that Lean's first coordinate `b.1` is the positive tail/base cube in
`Z0 \ Y0`.

Post-`b85079a` Lean target for the narrowest dictionary:

```lean
CMP116Eq231InteriorBoundaryToGapSource
```

with field:

```lean
∀ Z D b,
  bondInterior Z D b →
    bondBoundaryDisjoint Z D b →
      b.1 ∈ gapCubes Z D
```

The projection theorem is:

```lean
cmp116Eq231_interiorBoundary_to_gapCubes_of_source
```

and the existing positive-tail ownership route consumes it through:

```lean
CMP116Eq231PositiveTailOwnershipSource.of_interiorBoundaryToGapSource
```

Post-`57875f1` correction: the two-premise target above is too strong for the
registered source windows unless `bondInterior` secretly includes membership
in `Y0^{c,*}`.  Treat it as a sufficient Lean interface, not as the active
source extraction target.  The active target is:

```lean
CMP116Eq231Y0cStarInteriorBoundaryToGapSource
```

with field:

```lean
∀ Z D b,
  bondInY0cStar Z D b →
    bondInterior Z D b →
      bondBoundaryDisjoint Z D b →
        b.1 ∈ gapCubes Z D
```

and source-admissible bonds must separately supply:

```lean
CMP116Eq231FullCarrierAdmissibilitySource
```

The consumer route is:

```lean
CMP116Eq231PositiveTailOwnershipSource.of_y0cStarInteriorBoundary
cmp116Eq231_bond_fst_mem_gapCubes_of_y0cStarInteriorBoundary
```

Current decision after `b48b420`: the registered extraction does not yet prove
this three-premise theorem.  It proves the separate CMP116 clauses
`Y0^{c,*}`, interior, and no-`dZ0`, plus CMP109 endpoint/positive-orientation
context.  The unresolved sentence is:

```text
positive source bond b = (b_-, b_+) is encoded by the repository as
(b_-, direction), so Lean's first coordinate b.1 is the source tail/base b_-.
```

If this sentence cannot be sourced and only incidence/either-endpoint
membership is available, do not force `b.1 ∈ gapCubes`; switch the target to a
source-compatible incidence/endpoints carrier and redo the carrier count.

## Prompt B — membership iff

Extract the source-native theorem:

```lean
P ∈ PIndex Z D ↔ sourceAdmissible Z D P
```

Then connect it to the filtered Lean family only after admissible is source-defined, not vacuous.

## Prompt C — admissible iff without vacuity

Define `admissible` by source clauses: interior of `Z0`, no `dZ0` intersection, smallest localization domain containing `Y0` and `P`, and any additional CMP116 clauses.  Do not define it as `decide (P ∈ PIndex Z D)`.
