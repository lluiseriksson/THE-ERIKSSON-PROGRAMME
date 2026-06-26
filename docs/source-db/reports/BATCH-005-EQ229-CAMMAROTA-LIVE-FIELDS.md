# Batch 005 — CMP116 Eq. (2.29) / Cammarota live-field metadata

This batch is additive and operational. It adds source-db cards and indices for the Eq. (2.29) front, mirroring the precision Batch 004 gave to Eq. (2.31).

## Added catalog

```text
docs/source-db/catalogs/eq229-cammarota-live-fields.json
```

## Added indices

```text
docs/source-db/indices/EQ229-CAMMAROTA-LIVE-FIELDS.md
docs/source-db/indices/EQ229-CAMMAROTA-EXTRACTION-PROMPTS.md
docs/source-db/indices/EQ229-D-FAMILY-DICTIONARY-PLAN.md
docs/source-db/indices/CAMMAROTA-ACQUISITION-AND-CITATION-LEDGER.md
docs/source-db/indices/LLM-FAST-CONTEXT-UPDATE-BATCH-005.md
```

## New cards

```text
proof.eq229.live-fields.v2
proof.eq229.cammarota.theorem1.extraction-target.v2
proof.eq229.d-family.dictionary.v2
proof.eq229.thresholds.largeK-smallAlpha6.v2
request.cammarota.primary-access.ledger.v2
guard.eq229.no-bibliographic-closure.v2
proof.eq229.commit-sequence.v2
request.eq229.cmp116-local-excerpt-cleanup.v2
llm.eq229.fast-context.update.batch005
```

## Honest scope

No primary-source status is promoted. The batch does not prove Eq. (2.29), does not extract the Cammarota theorem, and does not discharge `CMP116Lemma3Eq229ScaleBoundary`. It makes the next source extraction sprint harder to derail.
