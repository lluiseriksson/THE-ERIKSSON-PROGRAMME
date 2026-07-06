# Flow/IR Live Fields

Purpose: make the CMP109/CMP119 flow and IR bridge searchable without treating the irrelevant-operator geometric contraction surrogate as a 4D marginal gauge-coupling beta-flow proof.

## Source Anchors

Open these first:

```powershell
python scripts\source_db.py show proof.flow.ir.bridge
python scripts\source_db.py show crosswalk.flow-ir-asymptotic-freedom-route
python scripts\source_db.py show cmp109.localization-domain-linear-size-dj
python scripts\source_db.py show cmp119.theorem1.rt-inductive-assumptions
```

The current card is an operational crosswalk. It separates already-formal logistic/geometric surrogate lemmas from the source-level marginal flow and IR covariance fields that still need a primary-source dictionary.

## Live Fields

| Field | Source target | Lean target | Status |
|---|---|---|---|
| marginal coupling recursion | CMP109/CMP119 beta-function or coupling-flow source statement | `YangMills.RG.BalabanCMP116SourceAssumptions.coupling_recursion` | dictionary_open |
| logarithmic flow regime | source distinction between marginal 4D gauge coupling and irrelevant contraction | `YangMills.RG.logistic_geometric_decay` blocker context | source_pending |
| irrelevant contraction | source theorem for irrelevant operator/remainder contraction | `YangMills.RG.remainder_geometric_of_logistic` | operational_surrogate |
| IR covariance bound | source IR covariance or large-distance decay statement | `YangMills.RG.BalabanCMP116SourceAssumptions.ir_bound` | dictionary_open |
| scale dictionary | source scale, block, and metric conventions linking CMP109/CMP119 to repository indices | flow/IR consumers in `YangMills.RG.BalabanCMP116SourceAssumptions` | dictionary_open |

## Non-Claims

- Do not use `g_k <= C*r^k` as a 4D marginal Yang-Mills coupling-flow theorem.
- Do not promote `YangMills.RG.logistic_geometric_decay` from an operational surrogate to source extraction.
- Do not infer `YangMills.RG.BalabanCMP116SourceAssumptions.ir_bound` from irrelevant-operator contraction alone.
- Do not use Flow/IR routing to backfill raw activity, H#, covariance/root, Wilson Hessian, mass gap, or Clay claims.

The useful next source step is to extract the exact CMP109/CMP119 beta-flow and IR covariance statements, then state the repository dictionary that keeps marginal logarithmic flow separate from irrelevant geometric contraction.
