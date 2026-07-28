# Right-edge ratio seam: high-grid diagnostic

**Registered before execution:** 2026-07-20  
**Status:** `DESIGN_ONLY`; no G5/G2/G6 promotion

The existing cancellation-preserving ratio judge becomes slightly negative on
the seam box `lambda=[2.32,2.325]` under its frozen `qgrid=80`, `rgrid=16`,
`thetagrid=4`, `phigrid=4` representation.  This isolated diagnostic fixes
the same exact box and all five registered delta bands while changing only the
spatial resolution to

```text
qgrid=160, rgrid=32, thetagrid=8, phigrid=8, Arb=200 bits.
```

The algebraic ratio `Q=P0/B0` and the pre-registered tail charges are
unchanged.  A result is design evidence only.  It cannot extend the candidate
union unless a fresh production/replay pair, exact row validator, geometry
splice, and tail/H-tail review are subsequently created.  A nonpositive row
retires this high-grid representation for the box.
