# K_D positive-floor probe (2026-07-21)

This note records a diagnostic probe for the denominator carrier `K_D` in the
K2 remainder route. It is **not** a promotion of G2 and does not remove any
manuscript slot.

## What was fixed

`surface_remainder_positive_kd_lower.py` previously multiplied positive Arb
balls directly. Near the reflected saddle, that ball product could have a
negative lower endpoint even though both factors were positive. The current
implementation takes lower endpoints factor-by-factor for the positive
polynomial, weight, reciprocal radius, and exponential. The exponential lower
endpoint is obtained from monotonicity, `exp(phase.lower())`, rather than from
an over-wide symmetric ball.

## Reproducible probes

The read-only driver is
`scripts/probe_surface_kd_floor_trefinement.py`. With

```
delta = 0.010 +/- 0.0005
t     = the 158 authoritative born t-boxes
grid  = 16 x 16 physical cells
```

it reports **158/158 positive rows, zero failures**. The smallest printed
lower endpoint is approximately `0.0712700349976479`, at parent box 111
(`t in [111/50, 56/25]`). The raw probe output is
`probe_kd_born_grid16.json` (SHA-256
`8C0F0E19F77E2F3272FB200EF53D50808D1C4072D17B27A5A4ED3B32FC6BC2C0`).

The script and lower-envelope implementation hashes for this local run are,
respectively, `864AA36CEA0E98C5AE535B9B6B5754EE3A20E7F5333755F64ED48A73033EF988`
and `40B8F8F3CAF36CECCC9A28E56577827E441CDB034DB36D7C28C0DC0D6BEEE739`.

An aggregate delta-union replay is now also recorded in
`run-records/legacy/surface-kd-floor-union-20260721.json`: three delicate
sub-unions use a 16x16 grid and the remaining interval uses 8x8, for **3002
rows and zero failures** over the full `[1/1000,1/15]` delta interval. Its
executable validator is `scripts/validate_surface_kd_floor_union.py`.

## Boundary of the claim

The KD union is still a carrier-floor probe, not the K2 remainder theorem. It
does **not** discharge the companion-tail ledger for `S1'''/S2'''`, and does
not provide the sign-to-`H_tail` splice. Consequently G2 remains
`REGULAR_008_AND_HYBRID_009_CERTIFIED`, G6 remains blocked, and the definitive
paper remains marked `DO_NOT_SUBMIT`.
