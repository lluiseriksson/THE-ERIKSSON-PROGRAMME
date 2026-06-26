# Worksheet — Eq. (2.31) `source_subset_gapCarrier`

## Exact target

```text
sourceAdmissible Z D P -> P subset gapCubes Z D × Fin 4
```

Preferred narrower target:

```text
sourceAdmissible Z D P -> forall b in P, b.1 in gapCubes Z D
```

because Lean already has a reducer from that premise to carrier containment.

## Allowed source keys

- `cmp116.eq231.p-family-carrier-source-target`
- `cmp109.bond-convention.positive-oriented`
- `crosswalk.eq231.p-family-source-dictionary-route`

## Required extraction fields

- What is the eligible bond universe?
- What is the source gap corresponding to `Z0 \ Y0`?
- Does each eligible positive-oriented bond have a unique base cube in that gap?
- Is the direction set exactly four positive directions, or only injects into them?

## Failure modes

- Using `|P| >= ...` as carrier upper bound.
- Counting unoriented bonds and getting factor 8.
- Treating CMP109 orientation as sufficient for CMP116 gap ownership.
