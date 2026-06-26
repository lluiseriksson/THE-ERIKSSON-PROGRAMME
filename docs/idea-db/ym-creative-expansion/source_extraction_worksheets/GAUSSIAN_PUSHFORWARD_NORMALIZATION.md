# Worksheet: Gaussian Pushforward Normalization

Mission: `OC_017_gaussian_pushforward_normalization`

## Target

```text
balabanCMP116Dmu0.map gaussianRootMap = physicalGaussian
```

## Guard

Record coordinate map, Jacobian/determinant normalization and measurability.

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
