# Incident: 160-bit diagnostic timeout on `[85,85.25]`

The preregistered diagnostic
`SURFACE-G2-CWIN3P2-P160-85-85P25-PREREG-20260725.md` changed only Arb
precision from 180 to 160 bits while retaining order 30/37, the five explicit
partitions, and `min_dt=1/100000`.  The wrapper
`scripts/run_surface_scaled_bulk_cwin3p2_high_split_p160_diagnostic.py` was
run on `[85,341/4]` for five minutes and emitted no terminal transcript.

The point-box improvement at `t=3` is therefore insufficient: the dominant
cost is not removed by precision alone.  No diagnostic output is admissible,
and the result does not alter G2/G6 or the authoritative 180-bit contract.

