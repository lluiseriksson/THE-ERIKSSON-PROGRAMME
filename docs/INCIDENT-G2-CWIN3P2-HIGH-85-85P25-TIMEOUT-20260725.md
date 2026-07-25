# Incident: high split timeout on `[85,85.25]`

The preregistered unit
`SURFACE-G2-CWIN3P2-HIGH-85-85P25-PREREG-20260725.md` was executed with the
current explicit-partition order-30/order-37 CWIN=`3/2` backend:

```text
python scripts/run_surface_scaled_bulk_cwin3p2_high_split.py \
  --unit 85_85p25_20260725 --lo 85 --hi 341/4
```

The production process reached the five-minute execution ceiling without
emitting a transcript or a terminal row.  No output or manifest is admitted.
This is an execution/design timeout, not evidence of either sign.  The beta
gap `[85,401/4]` therefore remains open and the result does not alter G2 or
G6.  A narrower rescue contract would require a new preregistration and a
fresh independent validation; there is no automatic promotion path.

