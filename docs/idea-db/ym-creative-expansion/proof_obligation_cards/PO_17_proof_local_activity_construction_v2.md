# Local activity construction/globalEval

**Key:** `proof.local-activity.construction.v2`
**Mission contract:** `OC_020_local_activity_construction_globalEval`
**Status:** `lean_linked / operational metadata only`

## Target shape

```text
(physicalActivity t k X).globalEval psi phi = balabanCMP116H ... X psi phi, with finite H(Z)/H(Z,Z0) index dictionary.
```

## Allowed source keys

- `cmp116.localized-activity.2.7-2.10`
- `cmp116.lemma3.window.2.14-2.38`
- `crosswalk.gaussian-root-activity-route`
- `proof.local-activity.construction.v2`

## Minimal success

- separate theorem target for construction identity
- D/P/Z0/Z0 prime dictionary listed
- termwise estimate kept as later field

## Reject if

- uses downstream H# or final Lemma 3 bound to prove an upstream field
- uses scalar Dimock architecture as a Yang-Mills theorem without a dictionary
- adds a monolithic raw-source package with the same live fields
- adds a downstream consumer while all old hypotheses remain
- uses final Lemma 3 estimate as construction identity

## Boundary

This card routes an agent to a source-backed theorem target.  It is not source
evidence and must not be cited as a mathematical proof.
