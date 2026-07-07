# Activity/Termwise Live Fields

Purpose: make the CMP116 `H(Z,Z0)` / `H(Z)` activity dictionary target directly searchable without treating rendered source displays as a Lean dictionary proof.

## Source Anchors

Open these first:

```powershell
python scripts\source_db.py show cmp116.localized-activity.2.7-2.10
python scripts\source_db.py show cmp116.lemma3.window.2.14-2.38
python scripts\source_db.py show proof.activity.termwise-identification
python scripts\source_db.py show proof.local-activity.construction.v2
python scripts\source_db.py show proof.raw-pointwise-decay.termwise.v2
python scripts\source_db.py show crosswalk.gaussian-root-activity-route
```

Focused blocker lookups:

```powershell
python scripts\source_db.py blockers source_to_lean_activity_identification_dictionary
python scripts\source_db.py blockers source_to_lean_termwise_estimate_dictionary
```

These should return the `proof.activity.termwise-identification` card and the
`proof.activity.termwise.live-fields.v2` live-field map. Use them to route the
exact open dictionary field before trying to feed
`YangMills.RG.CMP116Lemma3ActivityTermwiseScaleBoundary.activity_identification`
or
`YangMills.RG.CMP116Lemma3ActivityTermwiseScaleBoundary.termwise_estimate`.

`crosswalk.gaussian-root-activity-route` is the repository operational route
key, not a primary source. Keep it attached so agents see the route to
`YangMills.RG.LocalActivity.globalEval`, but do not use the crosswalk itself to
identify the printed `H(Z)` expansion with Lean local activity or to prove
`activity_identification`, `termwise_estimate`, or `raw_pointwise_decay`.

Archive cycle 47 visually confirms the CMP116 displays for `H(Z,Z0)`, `H(Z)`, and component factorization. That is render provenance only. The source-to-Lean dictionary is still open.

Field-uniformity locator: CMP116 printed p.15 frames the termwise-estimate window on `U^c_{k+1}(X, alpha0, alpha1)`. Printed p.16, around (2.20) and (2.22), contains the field-dependent estimates that still have to be matched to Lean field variables before `YangMills.RG.CMP116Lemma3ActivityTermwiseScaleBoundary.termwise_estimate` can be theorem-fed.

## Live Fields

| Field | Source target | Lean target | Status |
|---|---|---|---|
| activity identification | CMP116 (2.7)-(2.10) localized `H(Z,Z0)` / `H(Z)` displays | `YangMills.RG.CMP116Lemma3ActivityTermwiseScaleBoundary.activity_identification` | dictionary_open |
| index stack | CMP116 `Z`, `Z0`, components, and later `D/P/Z0/Z0'` resummation order | `YangMills.RG.LocalActivity.globalEval` summation indices | dictionary_open |
| summand identity | printed source summand in the finite `H(Z)` expansion | repository `R.summand` / local activity summand | dictionary_open |
| term weight | CMP116 termwise majorants around (2.14)-(2.38) | `YangMills.RG.CMP116Lemma3ActivityTermwiseScaleBoundary.termwise_estimate` | dictionary_open |
| component factorization | printed component factorization of `H(Z)` | finite-product / flat-sum compatibility theorem | dictionary_open |
| field uniformity | CMP116 printed p.15 `U^c_{k+1}(X, alpha0, alpha1)` analytic domain plus p.16 (2.20)/(2.22) field-dependent estimates | future source premise for termwise estimate | dictionary_open |

## Non-Claims

- Do not infer `activity_identification` from the existence of the printed `H(Z)` display.
- Do not infer `termwise_estimate` from the final Lemma 3 bound.
- Do not infer `raw_pointwise_decay` from a finite-sum norm bridge.
- Do not replace the source dictionary with a synthetic one-point summand or post-hoc termWeight.

The useful next source step is to extract a source-facing finite-sum dictionary for `H(Z)` first, then separately extract the termwise estimate and uniformity hypotheses.
