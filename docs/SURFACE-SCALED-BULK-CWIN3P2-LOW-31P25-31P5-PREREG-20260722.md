# CWIN=3/2 low scaled-bulk relay unit `[125/4,63/2]`

**Registered:** 2026-07-22, before execution  
**Scope:** candidate evidence only; no G2/G6 promotion

This is the next frozen quarter-width unit in the strict relay gap after the
validated `[31,125/4]` unit.  It fixes the order-30/order-37, 180-bit
CWIN=3/2 backend and requires adjacent negative `t` rows, byte-identical
production/replay, and dependency-hash validation.  The result must remain
quarantined and cannot alter the theorem manuscript.

```text
python scripts/run_surface_scaled_bulk_cwin3p2_high_unit.py --unit low_31p25_31p5 --lo 125/4 --hi 63/2
python scripts/run_surface_scaled_bulk_cwin3p2_high_unit.py --unit low_31p25_31p5 --lo 125/4 --hi 63/2 --replay
```
