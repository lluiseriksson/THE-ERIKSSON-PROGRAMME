# Unit-82 order-30 rescue slice

**Status:** candidate-only, quarantined; no G2/G6 or `(H_tail)` promotion.

The failed final unit `[275/4,69]` was subdivided at the first slice
`[275/4,1101/16]` (beta width `1/16`) and rerun with the same CWIN `3/2`
scaled backend at order 30 in beta and order 35 in `t`, Arb precision 220.
The adaptive cover passed with 167 strict-negative rows; the independent
replay is byte-identical.  The validator reports:

```text
UNIT82 ORDER30 RESCUE VALIDATION PASS rows 167
PRODUCTION/REPLAY BYTE EQUALITY PASS
```

The manifest is
`run-manifests/surface-scaled-bulk-cwin3p2-unit82-rescue-order30-20260723.json`.
This is a finite sign slice only.  Three further beta slices remain for the
unit, and even a complete order-30 cover would still need the independent
absolute relay to `(H_tail)` and the `M_supremum` budget before G2/G6 could
change state.
