# LLM Query Prompts — Batch 003

## Source extraction prompt

You are source-extracting for THE-ERIKSSON-PROGRAMME. Read `PROOF-OBLIGATION-CARDS.md`, choose exactly one card, inspect only the listed citation keys/pages first, and return:

1. exact primary-source statement;
2. formula with hypotheses and quantifiers;
3. source-symbol dictionary;
4. proposed Lean theorem statement;
5. hypothesis removed;
6. remaining blockers;
7. whether the citation may be promoted to `source_extracted`.

Do not add downstream consumers.

## Eq. (2.31) P-family prompt

Use source keys `cmp116.eq231.p-family-carrier-source-target`, `cmp109.bond-convention.positive-oriented`, and `crosswalk.eq231.p-family-source-dictionary-route`. Prove or state the exact missing lemma for:

```text
P in BalabanPFamily(Z,D)
  <-> P subset gapCubes(Z,D) x Fin 4 and admissible(Z,D,P)=true
```

Also prove or source-shape:

```text
|EligibleCarrier(Z0,Y0)| <= 4*|Z0 \ Y0|
```

Do not use the lower bound on `|P|` as a carrier upper bound.

## Eq. (2.29) Cammarota prompt

Use source keys `cmp116.eq229.d-stage-summability`, `cmp109.ref26.cammarota-infinite-range-cluster`, `cammarota.cmp85.polymer-mayer-source-target`, and `crosswalk.eq229.cammarota-dstage-route`. Extract the exact Cammarota theorem, smallness condition, constants, polymer metric convention, and dictionary to Balaban D-families.

Do not cite bibliography as theorem extraction.

## Eq. (2.37) prompt

Use `cmp116.eq237.post-p-resummation`, `cmp116.constants.c3-alpha5`, and `crosswalk.eq237.combined-postp-route`. Extract the fixed-Z0' estimate and the final post-(2.37) summation as separate source statements feeding `cmp116PostPResidualSourceBound_of_eq237`.

Do not split into source theorems unsupported by the paragraph order.

## Activity/termwise prompt

Use `cmp116.localized-activity.2.7-2.10`, `cmp116.lemma3.window.2.14-2.38`, `proof.activity.termwise-identification`, and `proof.activity.termwise.live-fields.v2`. First extract the finite `H(Z,Z0)` / `H(Z)` source-to-Lean dictionary; only then extract the termwise estimate.

Return the index stack, summand, termWeight, component-factorization compatibility, and field-uniformity blockers separately.

Do not claim `activity_identification` from render provenance alone, and do not claim `raw_pointwise_decay` from the final Lemma 3 bound.

## Support/measurability prompt

Use `proof.activity.support-measurability.v2`, `cmp116.localized-activity.2.7-2.10`, `proof.local-activity.construction.v2`, and repository `PhysicalGaugeCMP116Dictionary` support conventions. Extract support containment separately from adapted-field measurability.

Return the source localized domains, physicalActiveSupport enlargement convention, skeleton/physicalBondsOfCells dictionary, spectator support target, fluctuation support target, and measurability blocker separately.

Do not claim support from exponential decay, do not claim measurability from render provenance alone, and do not promote repository support conventions to primary-source theorems.

## H#/Appendix-F prompt

Use `proof.dimock.appendixf.hsharp-feed`, `proof.rooted-hsharp-remainder.identity.v2`, `crosswalk.dimock.appendixf-hole-cluster-route`, `dimockii.appendix-f.cluster-with-holes`, and `dimockii.appendix-f.second-ursell.645-646`. Extract the Appendix-F H# feed separately from the downstream rooted physical `Rsc` identity.

Return the CMP116/Balaban activity-bound feed, `H0`/`kappa` hypotheses, holes/Omega connectivity dictionary, skeleton metric dictionary, H# exponential weight loss, rooted-series target, summability, and real-part normalization blockers separately.

Do not claim raw-source construction, raw pointwise decay, or rooted H# identity from Dimock's scalar architecture alone.
