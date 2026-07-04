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
```

Archive cycle 47 visually confirms the CMP116 displays for `H(Z,Z0)`, `H(Z)`, and component factorization. That is render provenance only. The source-to-Lean dictionary is still open.

## Live Fields

| Field | Source target | Lean target | Status |
|---|---|---|---|
| activity identification | CMP116 (2.7)-(2.10) localized `H(Z,Z0)` / `H(Z)` displays | `CMP116Lemma3ActivityTermwiseScaleBoundary.activity_identification` | dictionary_open |
| index stack | CMP116 `Z`, `Z0`, components, and later `D/P/Z0/Z0'` resummation order | `PhysicalGaugeLocalActivity.globalEval` summation indices | dictionary_open |
| summand identity | printed source summand in the finite `H(Z)` expansion | repository `R.summand` / local activity summand | dictionary_open |
| term weight | CMP116 termwise majorants around (2.14)-(2.38) | `CMP116Lemma3ActivityTermwiseScaleBoundary.termwise_estimate` | dictionary_open |
| component factorization | printed component factorization of `H(Z)` | finite-product / flat-sum compatibility theorem | dictionary_open |
| field uniformity | uniformity of the termwise estimate on the intended field/domain variables | future source premise for termwise estimate | dictionary_open |

## Non-Claims

- Do not infer `activity_identification` from the existence of the printed `H(Z)` display.
- Do not infer `termwise_estimate` from the final Lemma 3 bound.
- Do not infer `raw_pointwise_decay` from a finite-sum norm bridge.
- Do not replace the source dictionary with a synthetic one-point summand or post-hoc termWeight.

The useful next source step is to extract a source-facing finite-sum dictionary for `H(Z)` first, then separately extract the termwise estimate and uniformity hypotheses.
