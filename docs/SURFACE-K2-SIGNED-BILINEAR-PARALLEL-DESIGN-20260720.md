# K2 signed-bilinear parallel resolution study (2026-07-20)

## Result

The preregistered signed-cell bilinear expression was evaluated on all 158
born `t` boxes for the endpoint lane `delta in [0,1/1000]`, using the existing
charged-tail formula and a fixed `96 x 96` quadrant grid.  The independent
process-pool runner returned **158/158 strict positive design margins** and
positive `KD(0)` on every row.  The printed margins are positive even at the
worst early box (index 2, approximately `0.943 +/- 5.62e-4`); the final box is
also positive (approximately `2.23 +/- 2.47e-3`).

The corresponding normalized fourth quotient coefficient `Y3` is finite on
every row, ranging from about `4.18` near `t=0` to about `11.48` before the
last box.  This is a substantial contraction relative to the frozen grid-48
probe, where the stress-box enclosure was about `125` (and the grid-24 value
was about `2.18e4`).  The contraction is obtained by forming
`KD*HDF-KF*HDD` before summing cells; it is not a new theorem assumption.

## Reproducibility record

The executable is
`scripts/surface_remainder_signed_bilinear_parallel_design.py` with
`--grid 96 --workers 8`.  It produced
`scripts/surface_remainder_signed_bilinear_parallel_design.json`.
The independent structural replay is
`scripts/validate_surface_remainder_signed_bilinear_parallel_design.py`; it
checks the 158 exact rational intervals, adjacency to `pi_hi`, pass flags,
and the design-only scope label.

```text
script SHA-256: 6FEA292DEFA20295A001E78F5155F85567AB7B04A1B678200DCA149926D4B3C5
JSON   SHA-256: A85A9779DE644E4C21A0593BB737CE99CD4C55473E347756C7DFCB5F83F7D9C8
validator SHA-256: 70763EFF368214971BDC40323F8D805EFF143AE43C0071499616E2F97156D43C
rows: 158; passes: 158; exact born cover: [0, pi_hi]
```

The runner is deliberately separate from the authoritative K2 production
driver.  It does not amend the frozen production grid, does not create a run
manifest, does not alter G2/G6, and cannot remove a manuscript slot.  A
terminal promotion still requires a preregistered resolution choice, a
provenance-bearing production transcript, an independent replay, the exact
`B(0)=0`/denominator audit, and the existing G2 relay review.

The Fable consultation requested for this route timed out before returning a
verified `claude-fable-5` result; no claim here relies on that consultation.
