# Weak-main covariance parallel v3 — execution preregistration (2026-07-28)

This contract supersedes the serial execution topology only.  It does not
change a parameter box, spatial box, precision, companion enclosure, tail
charge, or target.

## Frozen execution topology

Each `(delta_index,t_index)` box is a pure independent computation.  Use
exactly 12 spawned worker processes.  Each worker:

1. sets Arb precision to 180 bits;
2. recomputes the same uniform tail charges;
3. applies the frozen lane-specific grid ladder;
4. returns only deterministic decimal interval strings and indices.

The parent collects futures in arbitrary completion order, stores every
result, and prints rows only after sorting lexicographically by
`(delta_index,t_index)`.  Therefore scheduling cannot alter the canonical
transcript bytes.

Progress is written to a separate non-evidence file and never to canonical
stdout or stderr.  A worker failure does not abort the campaign: all 576 boxes
are completed, every unresolved box is printed as `FAILROW`, and the process
exits nonzero only after emitting the full failure map.

The lane contracts are:

```text
near: t=[21/10,31415927/10000000], grids 24,48
far:  t=[0,21/10], grids 24,48,96
```

Both use 18 delta boxes, 32 t boxes, side 12, order 4, `z0=20`, 180 bits,
and target `X_main>-1/20`.

Production and replay for each lane must use 12 workers, fresh canonical and
progress paths, empty canonical stderr, byte-identical canonical stdout, and
the independently preregistered decimal transcript validator.
