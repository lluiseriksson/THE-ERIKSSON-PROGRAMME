# CMP116 Eq. (2.29) / Cammarota live fields (Batch 005)

Purpose: stop future agents from treating the bibliographic Cammarota reference as if it were already a theorem-fed Eq. (2.29) proof.

## Current source keys to open first

```text
cmp116.eq229.d-stage-summability
cmp116.lemma3.window.2.14-2.38
cmp109.ref26.cammarota-infinite-range-cluster
cammarota.cmp85.polymer-mayer-source-target
proof.eq229.cammarota-dstage-summability
crosswalk.eq229.cammarota-dstage-route
```

## Live fields

| Field | Current state | Source task | Lean payoff |
|---|---|---|---|
| Cammarota theorem text | bibliographic metadata only | obtain clean primary theorem page and formula | feeds `CMP116Eq229Summability` |
| Thresholds | qualitative in CMP116 | dependencies for `K` large and `alpha6` small | formal source-bound package |
| D-family dictionary | not identified | map Balaban D families to `DIndex`/`DParts` | no arbitrary D-stage assumption |
| Metric convention | visually located | clean compact excerpt for (2.27)/(2.30) | source metric normalization |
| Product adaptation | pending | prove Cammarota theorem implies Eq. (2.29) product | `CMP116Lemma3Eq229ScaleBoundary` |

## Central target

```text
sum_D prod_{Y in D} alpha6 * exp(-delta*kappa*d_k(Y)) <= 1
```

This display is already visually located under `cmp116.eq229.d-stage-summability`, but it is not yet theorem-fed because the Cammarota theorem and the source-to-Lean D-family dictionary are missing.

## Anti-false-closure rule

```text
CMP109 reference [26] identifies Cammarota CMP85.
Springer confirms metadata and abstract relevance.
Neither is the theorem statement needed by Lean.
```

Do not claim Eq. (2.29) source closure until the exact theorem/lemma/proposition, hypotheses, constants, threshold dependencies, metric, and dictionary are extracted.
