# Gaussian/root/Hessian proof prompts — Batch 006

Use these prompts for focused agents. Each prompt must end with either a Lean theorem target or an explicit source blocker.

## 1. Covariance/root certificate

```text
Open `BalabanCMP116SourceAssumptions.covariance_root_certificate` and the citation keys
`cmp116.gaussian-pushforward.2.5-2.6` and `dimockii.fluctuation-covariance.271-276`.
Extract the exact theorem needed to populate `PhysicalLocalizedCovarianceRootCertificate` in the physical gauge types.
Do not claim the product-Gaussian pushforward proves the certificate.
Return: theorem statement, source locators, missing constants/dictionary fields.
```

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
