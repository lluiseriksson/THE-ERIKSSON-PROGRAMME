# CWIN=3/2 low scaled-bulk relay unit `[31,125/4]`

**Registered:** 2026-07-22, before execution  
**Scope:** candidate evidence only; no G2/G6 promotion

This is the first fresh unit in the strict relay gap `[31,74]`.  The
production and replay commands below are frozen before reading any result.
They use the CWIN=3/2 high-unit backend at beta order 30, `t_order=37`, and
180-bit Arb precision.  Acceptance requires adjacent terminal `t` rows,
strictly negative outward-rounded upper endpoints, byte-identical replay, and
matching dependency hashes in a quarantined schema-v1 manifest.

```text
python scripts/run_surface_scaled_bulk_cwin3p2_high_unit.py --unit low_31_31p25 --lo 31 --hi 125/4
python scripts/run_surface_scaled_bulk_cwin3p2_high_unit.py --unit low_31_31p25 --lo 31 --hi 125/4 --replay
```

Passing this unit would close only one candidate interval.  It would not prove
the finite-beta relay, the sign-to-`H_tail` implication, or any manuscript
claim.
