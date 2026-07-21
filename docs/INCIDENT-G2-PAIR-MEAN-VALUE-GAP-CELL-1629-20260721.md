# G2 pair mean-value gap cell (2026-07-21)

## Status

`CELL_CERTIFIED_CANDIDATE`; promotion remains `NONE`.

The preregistered 500-bit mean-value driver was run with production and
replay on

```text
beta   [1629/16, 3259/32]
lambda [3/2, 19/10]
modes 115, beta order 50, lambda order 50
```

Both transcripts are byte-identical and pass the exact-rational one-cell
cover audit.  The strict production upper endpoint is approximately
`-4.29037655702088e-109`.

The two-cell continuation adds the adjacent cell
`[3259/32,815/8]`, whose strict upper endpoint is approximately
`-3.96777275359578e-109`.  The combined manifest is
`run-manifests/surface-scaled-pair-mean-value-cover-beta1629p16-815p8-lambda150-190-20260721.json`.
This removes only the first `1/16` beta segment of the former topology gap;
the next dyadic cell `[1631/16,13049/128]` was subsequently run with the
same production/replay contract and passed with
`total_upper ≈ -3.6191967804e-109` (manifest
`surface-scaled-pair-mean-value-cell-beta101p9375-101p9453125-lambda150-190-20260721.json`).
The remaining interval up to `1000/9`, the scaled tail splice, and the
G2/G6 promotion are still open.  The manuscript slot and final-seal blockers
are therefore intentionally unchanged.

The next adjacent cell `[13050/128,13051/128]` also passed production and
replay, with `total_upper ≈ -3.4822689269e-109`; its candidate manifest is
`surface-scaled-pair-mean-value-cell-beta101p953125-101p9609375-lambda150-190-20260721.json`.
The continuous candidate coverage now reaches β=101.9609375, still with no
promotion.

The adjacent cell `[13051/128,13052/128]` also passed production and replay,
with `total_upper ≈ -3.4155935198e-109`; its manifest is
`surface-scaled-pair-mean-value-cell-beta101p9609375-101p96875-lambda150-190-20260721.json`.
The continuous candidate segment now reaches β=101.96875.  This remains a
candidate-only extension and leaves the final theorem gates unchanged.

Two more adjacent cells, `[13052/128,13053/128]` and
`[13053/128,13054/128]`, passed production and replay.  Their strict upper
endpoints are approximately `−3.35008e-109` and `−3.28571e-109`; the combined
manifest is
`surface-scaled-pair-mean-value-cover-beta101p96875-101p984375-lambda150-190-20260721.json`.
The candidate segment now reaches β=101.984375, still without G2/G6 load.
