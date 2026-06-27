# Eq. (2.31) narrow citation extraction requests

## CMP116 page 12

Open only the source window already registered by `cmp116.eq231.p-family-carrier-source-target`.
Extract:

- the auxiliary bond set for fixed `Y0`;
- how `chi_k` is decomposed into sums over `P`;
- how `Z0` is defined from `Y0` and `P`;
- what “interior of `Z0`” and “does not intersect `dZ0`” mean;
- whether every positive-oriented encoded bond has base cube in `Z0 \ Y0`.

## CMP116 pages 18–19

Extract only what is needed for:

- the P-family used in Eq. (2.31);
- the lower bound on `|P|`;
- the powerset/cardinality bracket;
- whether the carrier upper bound is stated or merely inferred.

## CMP109 orientation windows

Use CMP109 only for ambient convention:

- nearest-neighbor bonds;
- endpoints `(b_-, b_+)`;
- positive orientation.

Do not cite CMP109 alone as proving the CMP116 `P` carrier.

## Endpoint/base blocker after `1fed14e`

The next Lean target is:

```lean
CMP116Eq231InteriorBoundaryToGapSource
```

Extract only the source sentence or theorem needed for:

```lean
∀ Z D b,
  bondInterior Z D b →
    bondBoundaryDisjoint Z D b →
      b.1 ∈ gapCubes Z D
```

This then feeds:

```lean
CMP116Eq231PositiveTailOwnershipSource.of_interiorBoundaryToGapSource
```

and produces the broader positive-tail target:

```lean
∀ Z D P,
  sourceAdmissible Z D P →
    ∀ b : Cube × Fin 4,
      b ∈ P → b.1 ∈ gapCubes Z D
```

The exact missing source assertion is:

```text
For every bond b in a source-admissible Eq. (2.31) P-set, after CMP109
positive orientation b = (b_-, b_+) and repository encoding as
(b_-, direction), the base/tail endpoint b_- lies in Z0 \ Y0.
```

If CMP116 only says that the bond intersects or is incident to `Z0 \ Y0`,
that is not enough for the current `gapCubes × Fin 4` carrier.  It would
require a larger or incidence-based carrier, potentially with a factor 8 or
boundary-thickening instead of the current four-positive-direction count.

Do not use the Eq. (2.31) lower bound on `|P|` as a carrier upper bound.

## Corrected carrier-premise blocker after `57875f1`

The two-premise target above remains a useful sufficient interface, but the
registered CMP116/CMP109 material does not prove it.  The source-compatible
target keeps the carrier premise explicit:

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

Also extract the separate admissibility facts packaged as:

```lean
CMP116Eq231FullCarrierAdmissibilitySource
```

The exact missing source assertion is now:

```text
For every bond b in a source-admissible Eq. (2.31) P-set, CMP116 supplies
b in Y0^{c,*}, b is interior to Z0, and b does not meet dZ0; after CMP109
positive orientation b = (b_-, b_+) and repository encoding as
(b_-, direction), these three clauses imply the encoded first coordinate
b_- lies in Z0 \ Y0.
```

## Current local source-search result

The local text artifacts currently support only the split already represented
in Lean:

- `balaban-rg-II-cmp116-1104161193.txt` lines 467-475: for fixed `Y0`,
  CMP116 defines the auxiliary bond set, decomposes `chi_k` over `P`, takes
  `Z0` as the smallest localization domain containing `Y0` and `P`, and says
  bonds of `P` are contained in the interior of `Z0` and cannot intersect
  `dZ0`.
- `cmp116-pages-15-20.txt` lines 194-205: the Eq. (2.31) window says the
  fixed-`Z0` sum over `Y0,P` is controlled by the `|P|` exponential factor.
- `cmp116-pages-15-20.txt` lines 196-199: the OCR says the definition of `Z0`
  yields a `|P|` lower bound because one bond in `P` may connect two cubes in
  `Z0 \ Y0`.

These lines are useful evidence for the interior/no-boundary split and for the
gap-count heuristic, but they still do not identify Lean's first coordinate
`b.1` with the source base/tail cube in `Z0 \ Y0`.
