# Worksheet: Local Activity Global Eval

Mission: `OC_020_local_activity_construction_globalEval`

## Target

```text
physicalActivity.globalEval = balabanCMP116H
```

## Guard

Split construction identity from termwise norm estimate.

## Required extraction fields

- exact source key and page/equation locator;
- statement with quantifiers and hypotheses;
- constants and normalization conventions;
- source-symbol → Lean-symbol dictionary;
- `use_for` and `do_not_use_for` entries;
- Lean theorem target or exact blocker.

## Output

Return either a source-extracted candidate or a narrowed blocker.  Do not add a
downstream consumer unless the corresponding field is removed.
