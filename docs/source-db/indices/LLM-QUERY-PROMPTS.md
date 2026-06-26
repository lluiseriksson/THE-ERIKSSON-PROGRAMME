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
