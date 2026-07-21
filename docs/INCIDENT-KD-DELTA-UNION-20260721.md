# Incident: positive-KD union loses the endpoint seam

The factorized positive lower implementation was replayed over the first
positive-delta segment using the authoritative 158 born `t` boxes and an 8x8
physical grid:

```
delta union: [1/1000, 1/200]
delta width: 1/2000
rows: 8 * 158 = 1264
```

Seven delta boxes passed all 158 `t` boxes. The first box
`[1/1000, 3/2000]` failed in 45 late-`t` boxes (indices 112--156). The
printed lower endpoints were small negatives, from about `-1.1e-14` to
`-1.1e-11`; the first failure is at `t` index 112 and the magnitude grows
toward the reflected endpoint.

This is a diagnostic failure of the present companion/error enclosure at the
endpoint seam. It is not a sign counterexample for the exact positive carrier:
the endpoint lane already covers `delta <= 1/1000`, and the failures occur
only in the first positive box immediately beyond that lane. No parameter
narrowing, grid change, or delta-splice movement is promoted in response.

The raw probe is `probe_kd_delta_001_005_grid8.json`; the driver is
`scripts/probe_surface_kd_floor_delta_union.py`. The result does not close
the uniform `K_D` floor, the weighted `S1'''/S2'''` budgets, G2, or G6.
