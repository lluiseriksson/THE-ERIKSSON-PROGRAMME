# Raw-source field order gate

**Key:** `proof.rawsource.m3.live-fields.v2`
**Mission contract:** `OC_026_rawsource_field_order_gate`
**Status:** `lean_linked / operational metadata only`

## Target shape

```text
field_order_patch_gate: every removed field must have all prerequisite fields either previously theorem-fed or explicitly carried.
```

## Allowed source keys

- `proof.rawsource.m3.live-fields.v2`
- `docs.source-db.README`

## Minimal success

- script/checklist update enforcing order
- burndown vector updated
- no claim of theorem discharge

## Reject if

- uses downstream H# or final Lemma 3 bound to prove an upstream field
- uses scalar Dimock architecture as a Yang-Mills theorem without a dictionary
- adds a monolithic raw-source package with the same live fields
- adds a downstream consumer while all old hypotheses remain

## Boundary

This card routes an agent to a source-backed theorem target.  It is not source
evidence and must not be cited as a mathematical proof.
