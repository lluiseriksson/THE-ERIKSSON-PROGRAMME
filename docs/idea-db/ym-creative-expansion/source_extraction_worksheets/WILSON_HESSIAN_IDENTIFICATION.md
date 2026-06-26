# Worksheet: Wilson Hessian Identification

Mission: `OC_019_wilson_hessian_identification_dictionary`

## Target

```text
wilsonHessianIdentification t k
```

## Guard

Track sign, normalization and PhysicalGaugeCMP116Dictionary transport.

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
