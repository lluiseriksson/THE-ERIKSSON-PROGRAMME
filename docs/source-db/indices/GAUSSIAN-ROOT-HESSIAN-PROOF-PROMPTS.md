# Gaussian/root/Hessian proof prompts — Batch 006

Use these prompts for focused agents. Each prompt must end with either a Lean theorem target or an explicit source blocker.

## 1. Covariance/root certificate

```text
Open `BalabanCMP116SourceAssumptions.covariance_root_certificate`,
`proof.gaussian.covariance-root-certificate.v2`, and the citation keys
`cmp116.gaussian-pushforward.2.5-2.6`,
`cmp95.covariance-green.bounds-source-target`,
`cmp96.one-step-covariance-law-source-target`,
`cmp99.background-field-propagator-source-target`, and
`cmp102.variational-hessian-expansion-source-target`.
Extract the exact theorem needed to populate `PhysicalLocalizedCovarianceRootCertificate` in the physical gauge types.
Use `dimockii.fluctuation-covariance.271-276` only as scalar architecture.
Do not claim the product-Gaussian pushforward or the Dimock architecture proves
the certificate.
Return: theorem statement, source locators, missing constants/dictionary fields.
```

## Source-key and blocker invariant

For the covariance/root lane, the human prompts must keep the same blocker
shape as `proof.gaussian.root.localization-certificate` and
`proof.gaussian.covariance-root-certificate.v2`. Keep
`proof.root.localization.v2` and `proof.gaussian.pushforward.dictionary.v2`
attached as companion repository live-field cards, not primary sources. CMP116
(2.5)--(2.6) is a Gaussian pushforward anchor, CMP95 is visual-confirmed
Green/operator evidence, CMP96 is located label/page metadata for the one-step
covariance/root law, and CMP99/CMP102 are transport/Hessian companion routes.
These are not yet a theorem-feedable source-to-Lean dictionary.

Do not populate `PhysicalLocalizedCovarianceRootCertificate`,
`BalabanCMP116SourceAssumptions.covariance_root_certificate`,
`BalabanCMP116SourceAssumptions.root_localization`, or
`PhysicalGaugeCMP116LocalizedGaussianActivitySourceHypotheses.gaussian_pushforward`
until the coordinate dictionary, normalization/scale dictionary, CMP95/CMP96/CMP99
transport, CMP102 Hessian interface, and determinant/Jacobian boundary are
explicitly supplied.

## 2. Gaussian pushforward

```text
Open CMP116 (2.5)-(2.6). Prove or state the exact coordinate/Jacobian theorem needed for
`(balabanCMP116Dmu0 (Cube d L) lieDim).map ((D t k).gaussianRootMap (root t k)) = physicalGaussian t k`.
Do not discharge root localization or Hessian fields.
```

## 3. Root localization

```text
Open CMP116 (2.7)-(2.10) and Dimock II (271)-(276). Identify the exact source proposition
that the covariance-root-localized factors agree with the local activity support used by Lean.
If only a scalar analogy exists, record it as architecture, not a source theorem.
```

## 4. Wilson Hessian

```text
Find the exact source location where Balaban's Wilson action Hessian/second variation is identified with the operator transported by `PhysicalGaugeCMP116Dictionary`.
Return a theorem target for `wilsonHessianIdentification t k`.
Do not cite Lemma 3 or Appendix F as the Hessian identity.
```

## 5. Local activity and termwise estimate

```text
Open CMP116 (2.7)-(2.14) and the Lemma-3 window. Split construction from estimate:
(a) activity/globalEval identity;
(b) termwise summand norm estimate;
(c) final raw_pointwise_decay after Eq. (2.29)/(2.31)/(2.37).
Return separate Lean theorem targets for each.
```

## 6. Rooted H# identity

```text
Open Dimock Appendix F source keys and the repository `rooted_hsharp_remainder_identity` field.
State the physical Yang-Mills H# identity target without using it to prove Gaussian/root/Hessian fields.
Record Omega-connectivity/skeleton dictionary obligations.
```
