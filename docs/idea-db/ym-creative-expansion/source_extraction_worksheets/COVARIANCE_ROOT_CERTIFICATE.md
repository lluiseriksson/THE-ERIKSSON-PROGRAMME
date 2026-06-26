# Worksheet: Covariance Root Certificate

Mission: `OC_016_covariance_root_certificate_dictionary`

## Target

```text
PhysicalLocalizedCovarianceRootCertificate
```

## Guard

List operator identity, root square, PSD, norm and kernel weight fields.  Do not use Gaussian pushforward alone.

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
