# Mission OC_016_covariance_root_certificate_dictionary

Proof card: `proof.gaussian.covariance-root-certificate.v2`

Sharpen or discharge the covariance_root_certificate field with an exact source-to-Lean dictionary for PhysicalLocalizedCovarianceRootCertificate.

## Allowed source keys

- `cmp116.gaussian-pushforward.2.5-2.6`
- `dimockii.fluctuation-covariance.271-276`
- `cmp95.covariance-green.bounds-source-target`
- `cmp96.one-step-covariance-law-source-target`
- `proof.gaussian.covariance-root-certificate.v2`

## Target shape

```text
PhysicalLocalizedCovarianceRootCertificate precision covariance root covNormBound rootNormBound covWeight rootWeight, with operator identities/norm bounds/weights stated in the physical gauge type stack.
```

## Minimal success

- one source-extracted covariance/root theorem target or one Lean theorem feeding covariance_root_certificate
- exact list of still-carried constants and dictionary fields
- no discharge of gaussian_pushforward or root_localization unless separately proved

## Reject if

- uses downstream H# or final Lemma 3 bound to prove an upstream field
- uses scalar Dimock architecture as a Yang-Mills theorem without a dictionary
- adds a monolithic raw-source package with the same live fields
- adds a downstream consumer while all old hypotheses remain

## Evidence required

- exact source locators
- operator dictionary
- norm/weight constants
- Lean theorem target
