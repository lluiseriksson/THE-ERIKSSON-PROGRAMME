# Mission OC_019_wilson_hessian_identification_dictionary

Proof card: `proof.wilson.hessian.identification.v2`

Locate and package the Wilson Hessian/second-variation dictionary before any activity estimate consumes it.

## Allowed source keys

- `cmp116.localized-activity.2.7-2.10`
- `crosswalk.gaussian-root-activity-route`
- `proof.wilson.hessian.identification.v2`

## Target shape

```text
wilsonHessianIdentification t k, with sign, normalization and PhysicalGaugeCMP116Dictionary transport explicit.
```

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

## Evidence required

- source locator
- sign convention
- normalization convention
- dictionary theorem target
