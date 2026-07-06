# CMP116 Eq. (2.37) post-P live fields — Batch 007

This file is **operational metadata**, not a primary source. It tells agents how to use the existing CMP116 Eq. (2.37) citation keys without adding more downstream wrappers.

## Primary keys to open first

```text
cmp116.eq237.post-p-resummation
cmp116.constants.c3-alpha5
cmp116.lemma3.window.2.14-2.38
```

## Existing Lean route

The route already has theorem-generated consumers:

```text
YangMills.RG.cmp116PostPResidualSourceBound_of_eq237
YangMills.RG.cmp116PostPResidualSourceBound_of_eq237_globalIndex
YangMills.RG.cmp116PostPResidualSourceBound_of_eq237_sourceIndexMemIff
YangMills.RG.CMP116Lemma3WeightedPostPSourceScaleBoundary.of_eq237
YangMills.RG.CMP116Lemma3WeightedPostPScaleSourceAssumptions.of_eq237
YangMills.RG.CMP116Lemma3WeightedPostPScaleSourceAssumptions.lemma3_activity_estimate_of_eq237
```

The Z0/Z0prime dictionary card also routes the existing helpers
`YangMills.RG.cmp116Eq237Z0PrimeIndex_subset_global` and
`YangMills.RG.cmp116Eq237Z0Fiber_mem_iff`.

Do **not** add more wrappers unless they remove a live source premise.

## Live fields

| Field | Meaning | First proof target | First Lean consumer |
|---|---|---|---|
| `heq237_fixed` | fixed-`Z0'` Eq. (2.37) source estimate | `proof.eq237.fixed-z0prime-display.v2` | `YangMills.RG.cmp116PostPResidualSourceBound_of_eq237` |
| `hpost_eq237` | post-(2.37) final summation over `Z0'` / `Z \ Z0'` | `proof.eq237.post-summation.final-z0prime.v2` | `YangMills.RG.cmp116PostPResidualSourceMajorizationScaleFamily_of_eq237` |
| `dict_Z0_Z0prime` | source-to-Lean dictionary for `D/P/Z0/Z0'` and fibers | `proof.eq237.z0-z0prime-dictionary.v2` | `YangMills.RG.cmp116Eq237Z0Fiber`; `YangMills.RG.cmp116Eq237Z0Fiber_mem_iff`; `YangMills.RG.cmp116Eq237_nested_sum_eq_fiber_sum` |
| `component_product` | product over connected components `Z_i'` | `proof.eq237.component-product-to-family.v2` | `YangMills.RG.cmp116Eq237FixedZ0PrimeWeight`; `YangMills.RG.cmp116Eq237Amplitude` |
| `constant_majorants` | `alpha5`, `epsilon2`, `O(1)`, `C3` majorization | `proof.eq237.constant-majorants.alpha5-c3.v2` | `YangMills.RG.CMP116Eq237MajorizationBoundary`; `YangMills.RG.cmp116Eq237Amplitude` |
| `residual_budget` | seven-delta to eight-delta exponent reserve | `proof.eq237.residual-exponent-budget.v2` | `YangMills.RG.cmp116Eq237_residualExponent_absorbed` |

## Target shape to keep in mind

```text
fixed_Z0prime_bound + post_2_37_final_summation
  -> YangMills.RG.CMP116PostPResidualSourceBound
  -> YangMills.RG.CMP116PostPResidualSourceMajorizationScaleFamily
  -> Lemma 3 weighted post-P source assumptions
```

## Anti-patterns

```text
BAD: create a new Eq. (2.37) wrapper that still asks for heq237_fixed and hpost_eq237.
BAD: split Eq. (2.37) into standalone normalized Z0 and Z0prime theorems without source support.
BAD: use final Lemma 3 / C3 to backfill fixed-Z0prime source estimates.
GOOD: prove exactly one source premise or dictionary field, then feed the existing consumer.
```
