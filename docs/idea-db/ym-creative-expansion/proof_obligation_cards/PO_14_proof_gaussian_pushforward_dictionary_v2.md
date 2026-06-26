# Gaussian pushforward normalization

**Key:** `proof.gaussian.pushforward.dictionary.v2`
**Mission contract:** `OC_017_gaussian_pushforward_normalization`
**Status:** `lean_linked / operational metadata only`

## Target shape

```text
(balabanCMP116Dmu0 (Cube d L) lieDim).map ((D t k).gaussianRootMap (root t k)) = physicalGaussian t k, with normalization/Jacobian package explicit.
```

## Allowed source keys

- `cmp116.gaussian-pushforward.2.5-2.6`
- `dimocki.gaussian-normalization.66-74`
- `proof.gaussian.pushforward.dictionary.v2`

## Minimal success

- source-extracted pushforward theorem or Lean theorem target
- normalization/determinant/Jacobian stated or explicitly blocked
- no claim about covariance_root_certificate

## Reject if

- uses downstream H# or final Lemma 3 bound to prove an upstream field
- uses scalar Dimock architecture as a Yang-Mills theorem without a dictionary
- adds a monolithic raw-source package with the same live fields
- adds a downstream consumer while all old hypotheses remain
- claims visual pushforward display closes determinant/Jacobian normalization

## Boundary

This card routes an agent to a source-backed theorem target.  It is not source
evidence and must not be cited as a mathematical proof.
