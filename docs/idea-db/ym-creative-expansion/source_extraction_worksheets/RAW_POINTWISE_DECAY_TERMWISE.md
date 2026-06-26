# Worksheet: Raw Pointwise Decay Termwise

Mission: `OC_022_raw_pointwise_decay_termwise_composition`

## Target

```text
summand norm <= termWeight -> raw_pointwise_decay
```

## Guard

Requires activity identity and Eq. 2.29/2.31/2.37 dependencies.

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
