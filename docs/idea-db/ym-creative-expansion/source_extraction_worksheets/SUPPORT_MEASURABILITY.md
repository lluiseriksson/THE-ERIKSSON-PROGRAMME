# Worksheet: Support Measurability

Mission: `OC_021_support_measurability_activity`

## Target

```text
support subset + StronglyMeasurable
```

## Guard

Do not infer measurability from locality or decay.

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
