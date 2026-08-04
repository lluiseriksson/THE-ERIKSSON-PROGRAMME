# Incident: coarse-grid loss at the positive-KD endpoint seam

The factorized positive lower implementation was first replayed over the
first positive-delta segment using the authoritative 158 born `t` boxes and
an 8x8 physical grid:

```
delta union: [1/1000, 1/200]
delta width: 1/2000
rows: 8 * 158 = 1264
```

Seven delta boxes passed all 158 `t` boxes. The first box
`[1/1000, 3/2000]` failed in 45 late-`t` boxes (indices 112--156). The
printed lower endpoints were small negatives, from about `-1.1e-14` to
`-1.1e-11`.

The apparent failure was caused by the coarse spatial grid, not by the
companion/error enclosure. Replaying that same first delta box with the
16x16 physical grid gives 158/158 positive rows and zero failures
(`probe_kd_delta_001_0015_grid16.json`). The 8x8 result is retained only as a
falsification of that coarse grid. The endpoint lane still covers
`delta <= 1/1000`; the remaining work is an exhaustive 16x16 replay of the
whole positive-delta union and, separately, the weighted S1'''/S2''' ledger.

The raw coarse probe is `probe_kd_delta_001_005_grid8.json`; the corrected
probe is `probe_kd_delta_001_0015_grid16.json`; the driver is
`scripts/probe_surface_kd_floor_delta_union.py`. These probes do not close
the uniform `K_D` floor, the weighted `S1'''/S2'''` budgets, G2, or G6.
