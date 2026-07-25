# Incident — seeded grid still fails for beta width 2

**Date:** 2026-07-25  
**Attempt:** `85_87_seed64_20260725`  
**Driver:** `certify_bulk_beta_taylor_scaled_sign_rows_cwin3p2_seeded_grid.py`  
**Configuration:** CWIN `3/2`, beta-order `30`, t-order `37`, Arb precision
`180`, rational seed step `1/64`.

The seeded-grid repair closes the previously timing-out unit
`[85,341/4]`, but it does not support an arbitrarily wider beta Taylor box.
The run for `[85,87]` was stopped by the driver's explicit failure contract
at

```text
t = 1.66278076171875
RuntimeError: bulk failure near t=1.66278076171875
```

No transcript was produced and no gate state changed.  The result is a
negative diagnostic: the beta width, not only the initial t root, controls
the enclosure loss in this region.  The admissible next scale remains the
quarter-width unit `[85,85.25]` (or a separately preregistered narrower box);
no post-hoc widening is allowed.
