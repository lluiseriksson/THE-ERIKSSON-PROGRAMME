# Worksheet: Rsc Flow Ir Decoupler

Mission: `OC_025_rsc_flow_ir_decoupler`

## Target

```text
polymer local -> scalar Rsc -> flow/IR
```

## Guard

Do not rewrite polymer-local R bounds as scalar geometric decay without bridge.

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
