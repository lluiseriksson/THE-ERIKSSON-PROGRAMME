# Incident: post-1635/16 seeded-grid cell lost sign

The preregistered candidate cell
`[1635/16,409/4]` was run with the frozen CWIN=`3/2`, beta order `30`,
`t_order=37`, 180-bit Arb, and seeded t step `1/64` from
`SURFACE-G2-POST1635-SEEDED-PREREG-20260725.md`.

The driver aborted without a terminal transcript after approximately six
minutes at

```text
RuntimeError: bulk failure near t=3.1230851350487385
```

The output file was zero bytes; no manifest or candidate evidence was emitted.
This is a falsification of this frozen configuration only. It does not justify
changing beta width, Taylor orders, precision, seed step, or the authoritative
G2 status. The candidate gap `[1635/16,1000/9]` and
`RELAY_LEMMA_UNPROVED` therefore remain unchanged.

