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

The manifest is
`run-manifests/surface-scaled-pair-mean-value-cover-beta1629p16-1629p16plus1over32-lambda150-190-20260721.json`.
This removes only the first `1/32` beta cell of the former topology gap; it
does not close the remaining interval up to `1000/9`, prove the scaled tail
splice, or promote G2/G6.  The manuscript slot and final-seal blockers are
therefore intentionally unchanged.
