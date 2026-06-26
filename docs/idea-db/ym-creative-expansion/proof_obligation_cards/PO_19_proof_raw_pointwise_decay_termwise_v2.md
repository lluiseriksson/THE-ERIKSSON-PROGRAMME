# Raw pointwise decay/termwise estimate

**Key:** `proof.raw-pointwise-decay.termwise.v2`
**Mission contract:** `OC_022_raw_pointwise_decay_termwise_composition`
**Status:** `lean_linked / operational metadata only`

## Target shape

```text
norm summand <= termWeight and norm physicalActivity.globalEval <= amplitude * weight, with dependencies explicit.
```

## Allowed source keys

- `cmp116.lemma3.window.2.14-2.38`
- `cmp116.eq229.d-stage-summability`
- `cmp116.eq231.p-bond-sum`
- `cmp116.eq237.post-p-resummation`
- `proof.raw-pointwise-decay.termwise.v2`

## Minimal success

- termwise theorem target or exact blocker
- dependency list for Eq. 2.29/2.31/2.37
- no final finite-sum backfill

## Reject if

- uses downstream H# or final Lemma 3 bound to prove an upstream field
- uses scalar Dimock architecture as a Yang-Mills theorem without a dictionary
- adds a monolithic raw-source package with the same live fields
- adds a downstream consumer while all old hypotheses remain
- claims raw_pointwise_decay from final finite-sum bridge alone

## Boundary

This card routes an agent to a source-backed theorem target.  It is not source
evidence and must not be cited as a mathematical proof.
