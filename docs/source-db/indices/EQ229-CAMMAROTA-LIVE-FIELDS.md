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
| Cammarota theorem text | Archive-private holdings plus one visual Eq. (1.4) premise field; conclusion/thresholds still open | extract the remaining Theorem 1 conclusion, hypotheses, constants, compatibility relation, and uniformity | feeds `YangMills.RG.CMP116Eq229Summability` only after dictionary work |
| Thresholds | qualitative in CMP116 | dependencies for `K` large and `alpha6` small | formal source-bound package |
| D-family dictionary | not identified | map Balaban D families to `DIndex`/`DParts` | no arbitrary D-stage assumption |
| Metric convention | visually located | clean compact excerpt for (2.27)/(2.30) | source metric normalization |
| Product adaptation | pending | prove Cammarota theorem implies Eq. (2.29) product | `YangMills.RG.CMP116Lemma3Eq229ScaleBoundary` |

## Focused blocker lookups

Use the exact blocker filters when routing Eq. (2.29) work so the Cammarota,
D-family, and threshold gaps stay separate:

```text
python scripts\source_db.py blockers cammarota_theorem1_conclusion_half_rate_constants_dictionary_open
python scripts\source_db.py blockers d_family_to_DIndex_DParts_dictionary_open
python scripts\source_db.py blockers largeK_smallAlpha6_threshold_dependencies_dictionary_open
```

These are locator filters only.  They do not discharge the Cammarota Theorem 1
conclusion, the Balaban D-family dictionary, the large-K/small-alpha6 threshold
dependencies, or any Eq. (2.29) Lean theorem.

## Central target

```text
sum_D prod_{Y in D} alpha6 * exp(-delta*kappa*d_k(Y)) <= 1
```

This display is already visually located under `cmp116.eq229.d-stage-summability`, but it is not yet theorem-fed because the Cammarota theorem conclusion, smallness/constant hierarchy, and source-to-Lean D-family dictionary are missing.  The extracted Cammarota Eq. (1.4) potential-decay premise is only a single source-premise field; it does not supply the Mayer convergence theorem or Balaban Eq. (2.29).

## Lean finite-discharge interface

The verified Lean surface now includes two finite transport layers that reduce
the old target-field landing pad:

```lean
YangMills.RG.cmp116Eq229Summability_of_product_majorant
YangMills.RG.cmp116Eq229Summability_of_uniform_product_bound
YangMills.RG.CammarotaCMP85Threshold.of_product_majorant
YangMills.RG.CammarotaCMP85Threshold.of_uniform_product_bound
YangMills.RG.CammarotaCMP85FiniteDStageSource
YangMills.RG.CMP116Eq229Summability.of_cammarotaFiniteDStageSource
YangMills.RG.CammarotaCMP85Threshold.of_finiteDStageSource
```

These theorems do not extract Cammarota CMP85.  They say that once a source
theorem gives a finite Cammarota-side product sum, and a dictionary proves the
CMP116 Eq. (2.29) product is termwise bounded by that source product, Lean can
derive `YangMills.RG.CMP116Eq229Summability` without assuming that target predicate as a
primitive field.

## Anti-false-closure rule

```text
CMP109 reference [26] identifies Cammarota CMP85.
Springer confirms metadata and abstract relevance.
Neither is the theorem statement needed by Lean.
```

Do not claim Eq. (2.29) source closure until the exact theorem/lemma/proposition, hypotheses, constants, threshold dependencies, metric, and dictionary are extracted.
