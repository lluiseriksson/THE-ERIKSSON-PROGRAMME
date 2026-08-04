# Activity/Termwise Proof Prompts

## Source keys and routing invariant

```text
primary/source-side keys:
  - cmp116.localized-activity.2.7-2.10
  - cmp116.lemma3.window.2.14-2.38
operational route key (repository metadata; not a primary source):
  - crosswalk.gaussian-root-activity-route
```

Keep `crosswalk.gaussian-root-activity-route` attached as the public
operational route to `YangMills.RG.LocalActivity.globalEval` and
`YangMills.RG.CMP116Lemma3ActivityTermwiseScaleBoundary`. The crosswalk does
not identify the printed `H(Z)` resummation with Lean local activity by itself,
and it does not prove `activity_identification`, `termwise_estimate`, or
`raw_pointwise_decay`.

## Prompt A - H(Z) Dictionary

Open `cmp116.localized-activity.2.7-2.10` and inspect the visually confirmed CMP116 pages 13-14. Extract a Lean-facing dictionary statement for the finite `H(Z,Z0)` / `H(Z)` construction.

Return:

- source index variables and quantifiers;
- exact meaning of `Z`, `Z0`, connected components, and any localization domain;
- source summand shape, with field variables named;
- proposed Lean-side summation index type and `globalEval` equality;
- blockers that remain before `CMP116Lemma3ActivityTermwiseScaleBoundary.activity_identification`.

Do not use the final Lemma 3 estimate to prove this construction identity.

## Prompt B - Termwise Estimate

Open `cmp116.lemma3.window.2.14-2.38`. Extract only the termwise estimate source statement that could feed `CMP116Lemma3ActivityTermwiseScaleBoundary.termwise_estimate`.

Return:

- summand being estimated;
- termWeight expression;
- dependencies on `D`, `P`, `Z0`, `Z0'`, components, constants, and field variables;
- whether the estimate is field-uniform on `U^c_{k+1}(X, alpha0, alpha1)`, using printed p.15 for the domain and printed p.16 around (2.20)/(2.22) for the field-dependent estimates;
- remaining Eq. (2.29), Eq. (2.31), and Eq. (2.37) dependencies.

Do not claim `raw_pointwise_decay` from this prompt.

## Prompt C - Factorization Compatibility

Compare the printed component factorization of `H(Z)` with the repository flat finite-sum representation.

Return:

- exact source factorization statement;
- Lean representation that should consume it;
- whether a product-to-flat-sum theorem is needed;
- which source dictionary fields remain explicit.

Do not discharge a dictionary by renaming the factorization as a theorem.
