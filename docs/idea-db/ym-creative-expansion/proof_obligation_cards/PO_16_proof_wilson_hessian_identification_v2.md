# Wilson Hessian identification

**Key:** `proof.wilson.hessian.identification.v2`
**Mission contract:** `OC_019_wilson_hessian_identification_dictionary`
**Status:** `lean_linked / operational metadata only`

## Target shape

```text
wilsonHessianIdentification t k, with sign, normalization and PhysicalGaugeCMP116Dictionary transport explicit.
```

## Allowed source keys

- `cmp116.localized-activity.2.7-2.10`
- `crosswalk.gaussian-root-activity-route`
- `proof.wilson.hessian.identification.v2`

## Minimal success

- source locator for Hessian expansion or exact blocker
- Lean theorem target for wilsonHessianIdentification
- no use of final activity decay

## Reject if

- uses downstream H# or final Lemma 3 bound to prove an upstream field
- uses scalar Dimock architecture as a Yang-Mills theorem without a dictionary
- adds a monolithic raw-source package with the same live fields
- adds a downstream consumer while all old hypotheses remain
- cites Lemma 3 or Appendix F as Hessian identity

## Boundary

This card routes an agent to a source-backed theorem target.  It is not source
evidence and must not be cited as a mathematical proof.
