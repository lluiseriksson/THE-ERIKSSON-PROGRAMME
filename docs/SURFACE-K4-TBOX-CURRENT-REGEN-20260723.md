# Current-dependency K4 t-box regeneration

**Status:** candidate-only, quarantined; no theorem promotion.

The historical centred t-box ladder on `t∈[3,π]` was rejected by its own
validator because one dependency hash (`surface_remainder_centered_delta_carrier.py`)
had become stale.  I regenerated all 15 boxes against the current dependency
set, in separate files, and reran every box independently.

The reproducible audit now reports:

```text
units 15
cells 34560
domain 3 : 31415927/10000000
production/replay byte equality PASS
```

`compare_surface_remainder_k4_tbox_current_regen.py` also found exact
cell-by-cell equality with the historical transcripts after stripping only
the expected `git_head` line and the stale carrier digest.  Thus the
regeneration changes provenance, not the numerical evidence.  The manifest is
`run-manifests/surface-remainder-k4-tbox-current-regen-20260723.json`.

This still does **not** prove the weighted K4 statement or the global
`S1'''/S2'''` remainder: endpoint regularity, overlaps, weighted transport,
and the G2/G6 relay remain separate gates.
