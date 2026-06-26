# Batch 004 — Eq. (2.31) source-package live-field index

Batch 004 is a repository-alignment and hypothesis-removal navigation batch.

It adds one new operational catalog:

```text
docs/source-db/catalogs/eq231-source-package-live-fields.json
```

and four human indices:

```text
docs/source-db/indices/EQ231-SOURCE-PACKAGE-LIVE-FIELDS.md
docs/source-db/indices/EQ231-FIELD-DISCHARGE-PROMPTS.md
docs/source-db/indices/EQ231-SOURCE-DICTIONARY-COMMIT-QUEUE.md
docs/source-db/indices/EQ231-CITATION-EXTRACTION-REQUESTS.md
docs/source-db/indices/LLM-FAST-CONTEXT-UPDATE-BATCH-004.md
```

## What changed conceptually

The latest Eq. (2.31) route has enough downstream propagation.  The useful frontier is now the source package fields:

```text
source_subset_gapCarrier
mem_iff_source
admissible_iff_source
```

The repository has a theorem reducing `source_subset_gapCarrier` to the smaller premise that every encoded source bond has its first coordinate in `gapCubes`.  Batch 004 makes this the top-ranked source-discharge target.

## Status honesty

All new records are `lean_linked` operational metadata.  No paper citation is promoted to `source_extracted` by this batch.

## Recommended next implementation commit

```text
feat(RG): prove Eq231 bond base-cube ownership from source carrier
```

Payload:

```lean
cmp116Eq231_bond_fst_mem_gapCubes_of_sourceAdmissible
```

Then use:

```lean
cmp116Eq231_source_subset_gapCarrier_of_bond_fst_mem_gapCubes
```

Do not add more downstream consumers.
