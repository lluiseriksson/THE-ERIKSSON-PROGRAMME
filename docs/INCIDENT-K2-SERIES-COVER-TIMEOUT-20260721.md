# K2 endpoint-series cover timeout (2026-07-21)

**Status:** `DESIGN_TIMEOUT`; no gate promotion.

The existing design driver
`scripts/surface_remainder_delta0_series_cover_design.py` was run under a
300-second wall-clock budget at its registered 158 boxes of width `1/50` on
`t∈[0,π]`. It completed the first 30 boxes, through `t=0.6`, all at grid 96,
with positive margins (approximately `0.47` at the early boxes), but did not
finish the cover before the operational timeout.

This is an execution-cost result, not a mathematical failure. The driver is
explicitly design-only: its endpoint-series path still carries the order-four
companion charge and has no terminal production/replay manifest. The already
authoritative regular K2 transcripts are unaffected. A future terminal run
must use a bounded, resumable partition and the order-five companion route,
then emit the full 158-box provenance/replay object before any gate change.
