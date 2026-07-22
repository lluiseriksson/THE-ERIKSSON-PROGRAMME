# Pair mean-value next cell (2026-07-22)

The fixed configuration was rerun on the next dyadic cell after the existing
candidate archive:

```text
beta  [13057/128,13058/128] = [102.0078125,102.015625]
lambda [3/2,19/10]
modes 115; beta/lambda orders 50/50; Arb 500 bits
```

The first bounded attempt timed out at 120 seconds without output.  A fresh
run with a 600-second ceiling completed in 130.3 seconds; production and
replay were then written by the frozen runner and are byte-identical.  The
strict upper endpoint is
`-3.0391945389046818808539063904555120205e-109`.

The cell is archived as `CELL_CERTIFIED_CANDIDATE` with promotion `NONE` in
the accompanying manifest.  It does not repair the remaining beta union, does
not prove the sign-to-`H_tail` relay, and carries no G2/G6 load.
