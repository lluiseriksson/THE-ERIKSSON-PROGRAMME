# CWIN=3/2 low scaled-bulk relay unit `[22,89/4]`

**Registered:** 2026-07-22, before the fresh production/replay rerun  
**Scope:** candidate evidence only; no automatic G2/G6 promotion

This preregistration repairs the provenance defect of the earlier post-hoc
diagnostic for the same interval.  It fixes the CWIN=3/2 backend, the
order-30/order-37, 180-bit arithmetic, the exact beta interval
`[22,89/4]`, and the generic high-unit driver.  The production and replay
transcripts must be byte-identical, contain adjacent terminal `t` rows whose
upper endpoints are strictly negative, and carry matching dependency hashes.

Acceptance requires the dedicated validator to pass and the run manifest to
record the result as a quarantined candidate.  This unit does not prove the
finite-beta relay, the sign-to-`H_tail` implication, the moving-edge splice,
or any manuscript claim.

Commands fixed before execution:

```text
python scripts/run_surface_scaled_bulk_cwin3p2_high_unit.py --unit low_22_89_4 --lo 22 --hi 89/4
python scripts/run_surface_scaled_bulk_cwin3p2_high_unit.py --unit low_22_89_4 --lo 22 --hi 89/4 --replay
```
