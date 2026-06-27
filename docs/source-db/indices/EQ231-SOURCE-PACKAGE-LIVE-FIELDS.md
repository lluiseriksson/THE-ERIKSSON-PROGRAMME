# CMP116 Eq. (2.31) source-package live fields — Batch 004

Purpose: align the source database with the current post-`1fed14e` route.  The
repository already has conditional theorems routing the Eq. (2.31) carrier
through `CMP116Eq231PositiveTailOwnershipSource`, so the next progress must
prove one of the remaining source-native fields, not add downstream wrappers.

Refresh note after `1fed14e`: direct source-text inspection confirms the current
split.  CMP116 page 12 supports that source-admissible `P`-bonds are interior
to `Z0` and do not meet `dZ0`; the pages 18-19 OCR also contains the
`Z0 \ Y0` gap/count discussion near Eq. (2.31).  These windows still do not
prove the source-to-Lean dictionary
`sourceAdmissible Z D P -> b in P -> b.1 in gapCubes Z D`.  That dictionary,
or a corrected larger carrier if the source only gives incidence, remains the
live blocker.

Visual recheck after `4432292`: the local page renders for CMP116 pages 12,
18, and 19, plus the CMP109 `b0(c)` corridor page, confirm the same boundary.
The sources show `P ⊂ Y0^{c,*}`, smallest `Z0` containing `Y0` and `P`,
interior/no-`dZ0`, the `|P|` lower-bound rationale from bonds connecting cubes
in `Z0 \ Y0`, and the `b0(c)` corridor definition.  They still do not prove
that Lean's first coordinate `b.1` is the positive tail/base cube in
`Z0 \ Y0`.

Post-`b85079a` source-lock: Lean now names the exact remaining
interior/boundary dictionary as:

```lean
CMP116Eq231InteriorBoundaryToGapSource
cmp116Eq231_interiorBoundary_to_gapCubes_of_source
CMP116Eq231PositiveTailOwnershipSource.of_interiorBoundaryToGapSource
cmp116Eq231_bond_fst_mem_gapCubes_of_interiorBoundaryToGapSource
```

These declarations are record projection and assembly only.  They do not prove
that the currently registered CMP116/CMP109 windows discharge the
endpoint/base theorem.

Post-`57875f1` correction: the two-premise lock above is a sufficient Lean
interface, but it is too strong as a source target.  The source windows keep
`P ⊂ Y0^{c,*}` separate from the interior/no-`dZ0` clause.  The corrected
source-lock target is:

```lean
CMP116Eq231FullCarrierAdmissibilitySource
CMP116Eq231Y0cStarInteriorBoundaryToGapSource
cmp116Eq231_y0cStarInteriorBoundary_to_gapCubes_of_source
CMP116Eq231PositiveTailOwnershipSource.of_y0cStarInteriorBoundary
cmp116Eq231_bond_fst_mem_gapCubes_of_y0cStarInteriorBoundary
```

This keeps the explicit `bondInY0cStar` premise live instead of inferring gap
ownership from interior/no-boundary alone.

Post-`b48b420` endpoint/base audit: the corrected three-premise source-lock is
mathematically plausible, but the registered CMP116/CMP109 extraction still
does not prove it as a Lean-ready theorem.  The already-supported facts are:

```text
P subset Y0^{c,*}
P-bonds are interior to Z0
P-bonds do not meet dZ0
CMP109 writes bonds as b = (b_-, b_+) and uses positive orientation windows
```

The remaining missing dictionary is:

```text
positive source bond b = (b_-, b_+) is encoded in Lean as (b_-, direction),
so Lean's first coordinate b.1 is the source tail/base endpoint b_-.
```

If the source proves only incidence with `Z0 \ Y0` or either-endpoint
membership, the current four-direction carrier `gapCubes Z D × Fin 4` must be
replaced by an incidence/endpoints carrier with a different count.

Post-`33db1d4` incidence fallback: Lean now names the source-neutral fallback
carrier and its count:

```lean
cmp116Eq231IncidenceCarrier
cmp116Eq231_source_subset_incidenceCarrier_of_endpoint_mem_gapCubes
cmp116Eq231IncidenceCarrier_card
cmp116Eq231IncidenceCarrier_endpoint_mem_gapCubes
cmp116Eq231IncidenceCarrier_card_le_eight_scale4_gapMass
cmp116Eq231IncidenceGapMass
cmp116Eq231IncidenceCarrier_card_le_four_scale4_incidenceGapMass
cmp116Eq231IncidenceSourcePIndex
cmp116Eq231IncidenceSourcePIndex_mem_iff
cmp116Eq231IncidenceSourcePIndex_subset_carrier
CMP116Eq231PBondBoundary.of_incidenceSourceBondSets
CMP116Eq231PBondBoundary.of_incidenceFilteredBondSets
```

This carrier is `gapCubes Z D × Fin 4 × Fin 2`, represented as
`(Cube × Fin 4) × Fin 2`, and its finite count is `8 * |gapCubes Z D|`.  It is
wired into the generic `PBondBoundary` shape only through the doubled fallback
mass `cmp116Eq231IncidenceGapMass = 2 * cmp116Eq231GapMass`; it must not be
used as a drop-in replacement without a separate source retargeting of the
`P` family and summation normalization.

## Live fields

| Field | Best next theorem | Source keys | Removes | Status |
|---|---|---|---|---|
| `source_subset_gapCarrier` | `bond_fst_mem_gapCubes` then apply `cmp116Eq231_source_subset_gapCarrier_of_bond_fst_mem_gapCubes` | `cmp116.eq231.p-family-carrier-source-target`, `cmp109.bond-convention.positive-oriented` | carrier containment premise | narrowed, still source-pending |
| incidence fallback | endpoint-witness containment then apply `cmp116Eq231_source_subset_incidenceCarrier_of_endpoint_mem_gapCubes` | endpoint/base audit result if positive-tail fails | exact fallback carrier/count with doubled mass | Lean carrier/boundary exists; source retargeting open |
| `mem_iff_source` | `P ∈ PIndex ↔ sourceAdmissible Z D P` | `cmp116.eq231.p-family-carrier-source-target` | filtered PIndex dictionary | open |
| `admissible_iff_source` | `admissible Z D P = true ↔ source clauses` | CMP116 page-12/page-18/19 P-family text | anti-vacuity for admissible | open |
| pointwise P residual | `pResidualWeight ≤ constant * pGeometryWeight` | CMP116 Eq. (2.31) analytic window | P-stage analytic bound | separate analytic blocker |

Lean also has the honest fallback record:

```lean
CMP116Eq231PositiveTailOwnershipSource
```

This narrows the carrier branch to one source theorem:

```lean
∀ Z D P,
  sourceAdmissible Z D P →
    ∀ b : Cube × Fin 4,
      b ∈ P → b.1 ∈ gapCubes Z D
```

`CMP116Eq231EligibleBondCarrierSource.of_positiveTailOwnership` then supplies
the eligible-bond carrier record with
`sourceEligibleBond Z D b := b.1 ∈ gapCubes Z D`.  This avoids claiming a full
source-side eligible-bond iff until CMP116/CMP109 explicitly identify the
endpoint/base convention.

The page-12 source clause is now split before this one-field target:

```lean
CMP116Eq231InteriorBoundaryAdmissibilitySource
CMP116Eq231InteriorBoundaryToGapSource
cmp116Eq231_interiorBoundary_to_gapCubes_of_source
CMP116Eq231PositiveTailOwnershipSource.of_interiorBoundary
CMP116Eq231PositiveTailOwnershipSource.of_interiorBoundaryToGapSource
cmp116Eq231_bond_fst_mem_gapCubes_of_interiorBoundary
cmp116Eq231_bond_fst_mem_gapCubes_of_interiorBoundaryToGapSource
CMP116Eq231BalabanPFamilySourcePackage.of_interiorBoundary
```

This records only what CMP116 page 12 supports directly: source-admissible
`P`-bonds are interior to `Z0` and do not meet `dZ0`.  The remaining carrier
blocker is the separate source-to-Lean geometric dictionary proving that such
interior/boundary-disjoint encoded bonds also known to lie in `Y0^{c,*}` have
first coordinate in `gapCubes Z D`.

At package level,
`CMP116Eq231BalabanPFamilySourcePackage.of_interiorBoundary` now composes this
split with the existing source package constructor.  It removes the need for a
caller-supplied `CMP116Eq231PositiveTailOwnershipSource` record on this route,
but still requires the exact geometric dictionary
`bondInY0cStar ∧ bondInterior ∧ bondBoundaryDisjoint -> b.1 in gapCubes` on
the active source-audited route.

The positive-tail record now also feeds the immediate filtered-family route:

```lean
cmp116Eq231_sourcePIndexMemIff_of_positiveTailOwnership
CMP116Eq231PBondBoundary.of_positiveTailOwnership
CMP116Lemma3PStageSourceScaleBoundary.of_eq231_positiveTailOwnership
CMP116Lemma3WeightedPostPScaleSourceAssumptions.of_eq231_positiveTailOwnership
```

These are proof-assembly routes only.  They replace a raw `hPcarrier` input by
the named positive-tail source record plus the still-live membership and
admissibility dictionaries; they do not prove the positive-tail source theorem.

## Immediate rule

A commit is useful only if it removes one of the live fields above or proves a source-shaped premise that feeds an existing remover.  Another theorem forwarding `hPIndex`, `hPcarrier` or `CMP116Eq231PBondBoundary` without shrinking assumptions is cosmetic.

## Smallest high-payoff target

```lean
∀ Z D b,
  bondInY0cStar Z D b →
    bondInterior Z D b →
      bondBoundaryDisjoint Z D b →
        b.1 ∈ gapCubes Z D
```

This is now named by `CMP116Eq231Y0cStarInteriorBoundaryToGapSource`.  Once
this exact source-lock target is available, it feeds:

```lean
CMP116Eq231PositiveTailOwnershipSource.of_y0cStarInteriorBoundary
```

and yields the older source-admissible premise:

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

Do not promote this theorem from the current source packet.  The current packet
decides the audit negatively: it has not yet sourced `b.1 = b_-` or the
repository encoding step.
