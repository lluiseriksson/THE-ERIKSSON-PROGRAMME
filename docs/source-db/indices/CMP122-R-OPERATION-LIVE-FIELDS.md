# CMP122 R-Operation Live Fields

Purpose: keep the CMP119/CMP122 polymer-local R-operation certificate fields searchable without turning visual formula fields into a RawYMActivityDecay proof.

## Source Anchors

Open these first:

```powershell
python scripts\source_db.py show proof.cmp122.r-operation-polymer-local-bound
python scripts\source_db.py show crosswalk.r-operation-polymer-local-route
python scripts\source_db.py show cmp122ii.theorem1.coupling-interval-induction
python scripts\source_db.py show cmp122ii.rprime-bound.1.98-1.100
python scripts\source_db.py show cmp122ii.post-r-action-split.1.101
python scripts\source_db.py show cmp122i.large-field-c-bound.1.70
python scripts\source_db.py show cmp119.density-expansion-form.2.18
python scripts\source_db.py show cmp119.b-term-local-regularity-bound.2.34-2.42
```

The CMP122-I/II visual fields are source anchors only. The source-to-Lean dictionary for the post-R action, polymer metric, component split, and CMP119 Sect. 2 handoff is still open.

## Live Fields

| Field | Source target | Lean target | Status |
|---|---|---|---|
| theorem handoff | CMP122-II Theorem 1 small-coupling and CMP119 Sect. 2 conditions | `CMP119CMP122ERBSourceDecomposition` / `CMP116RawSourceM3Frontier` | dictionary_open |
| R-prime expansion | CMP122-II (1.98) exponentiated `R'^(k)` cluster expansion | future source certificate for `rloc_decay` | visual_formula_field_extracted_dictionary_open |
| R-prime pre-split bound | CMP122-II (1.99) with the `d_{k, union Y_i}(X)` metric | source metric/domain dictionary | visual_formula_field_extracted_dictionary_open |
| R-prime second-group bound | CMP122-II (1.100) with `exp(-p_0(g_k))` and `d_k(X)` | local R component decay input | visual_formula_field_extracted_dictionary_open |
| post-R action split | CMP122-II (1.101)-(1.102) first-group boundary versus second-group R terms | post-R action/local-activity dictionary | dictionary_open |
| large-field C bound | CMP122-I (1.70) `C_k^(n)` bound | B/local or component dictionary context | visual_formula_field_extracted_dictionary_open |
| CMP119 E/R/B handoff | CMP119 (2.18)-(2.42) density form, E/R/B pieces, and reserve conditions | `RawYMActivityDecay` route only after dictionaries | dictionary_open |

## Non-Claims

- Do not replace the polymer-local R-operation certificate with a bare scalar `R_k <= M*r^k`.
- Do not infer `RawYMActivityDecay` from CMP122-I/II visual formula fields.
- Do not infer component decay or `PhysicalGaugeLocalActivity.globalEval` equality from the post-R action split alone.
- Do not use CMP122-I (1.70) as a final post-R surrogate without the CMP119/CMP122 dictionary.

The useful next source step is to extract CMP122-II Theorem 1 hypotheses and the CMP119 Sect. 2 handoff first, then keep R-prime bounds, post-R action split, large-field C bounds, and CMP119 E/R/B handoff as separate certificate fields.
