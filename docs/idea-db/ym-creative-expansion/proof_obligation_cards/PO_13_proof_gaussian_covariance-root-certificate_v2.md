# Covariance/root certificate

**Key:** `proof.gaussian.covariance-root-certificate.v2`
**Mission contract:** `OC_016_covariance_root_certificate_dictionary`
**Status:** `lean_linked / operational metadata only`

## Target shape

```text
PhysicalLocalizedCovarianceRootCertificate precision covariance root covNormBound rootNormBound covWeight rootWeight, with operator identities/norm bounds/weights stated in the physical gauge type stack.
```

## Allowed source keys

- `cmp116.gaussian-pushforward.2.5-2.6`
- `dimockii.fluctuation-covariance.271-276`
- `cmp95.covariance-green.bounds-source-target`
- `cmp96.one-step-covariance-law-source-target`
- `proof.gaussian.covariance-root-certificate.v2`

## Minimal success

- one source-extracted covariance/root theorem target or one Lean theorem feeding covariance_root_certificate
- exact list of still-carried constants and dictionary fields
- no discharge of gaussian_pushforward or root_localization unless separately proved

## Reject if

- uses downstream H# or final Lemma 3 bound to prove an upstream field
- uses scalar Dimock architecture as a Yang-Mills theorem without a dictionary
- adds a monolithic raw-source package with the same live fields
- adds a downstream consumer while all old hypotheses remain

## Boundary

This card routes an agent to a source-backed theorem target.  It is not source
evidence and must not be cited as a mathematical proof.
