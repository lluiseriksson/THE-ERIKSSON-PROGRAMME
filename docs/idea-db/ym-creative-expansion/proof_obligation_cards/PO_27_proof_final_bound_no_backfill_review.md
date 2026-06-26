# Final-bound no-backfill review

**Key:** `proof.final-frontier.pipeline`
**Mission contract:** `OC_030_final_bound_no_backfill_review`
**Status:** `lean_linked / operational metadata only`

## Target shape

```text
final-bound patch may consume upstream fields but cannot prove them.
```

## Allowed source keys

- `cmp116.lemma3.final-2.38`
- `cmp116.effective-action.2.39-2.41`
- `crosswalk.final-frontier-pipeline`

## Minimal success

- review checklist update
- patch intake hard fail examples
- no upstream field removed unless separately evidenced

## Reject if

- uses downstream H# or final Lemma 3 bound to prove an upstream field
- uses scalar Dimock architecture as a Yang-Mills theorem without a dictionary
- adds a monolithic raw-source package with the same live fields
- adds a downstream consumer while all old hypotheses remain
- final bound is cited as source dictionary

## Boundary

This card routes an agent to a source-backed theorem target.  It is not source
evidence and must not be cited as a mathematical proof.
