# Worksheet: Appendix F Hsharp Geometry

Mission: `OC_023_appendix_f_hsharp_geometry_feed`

## Target

```text
Omega-connected H# geometry
```

## Guard

Keep Appendix F as consumer of rawSource, not source for upstream fields.

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
