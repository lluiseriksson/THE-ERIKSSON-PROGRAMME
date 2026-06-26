# Mission OC_017_gaussian_pushforward_normalization

Proof card: `proof.gaussian.pushforward.dictionary.v2`

Discharge only gaussian_pushforward by extracting the coordinate/Jacobian theorem behind CMP116 (2.5)-(2.6).

## Allowed source keys

- `cmp116.gaussian-pushforward.2.5-2.6`
- `dimocki.gaussian-normalization.66-74`
- `proof.gaussian.pushforward.dictionary.v2`

## Target shape

```text
(balabanCMP116Dmu0 (Cube d L) lieDim).map ((D t k).gaussianRootMap (root t k)) = physicalGaussian t k, with normalization/Jacobian package explicit.
```

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

## Evidence required

- CMP116 locator
- coordinate dictionary
- normalization/Jacobian evidence
- measurability requirement
