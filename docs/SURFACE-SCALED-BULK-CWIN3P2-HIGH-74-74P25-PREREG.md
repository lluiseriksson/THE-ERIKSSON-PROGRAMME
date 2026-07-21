# CWIN=3/2 high-order box [74, 74.25] — preregistration

**Registered before the terminal rerun:** 2026-07-21

This document fixes one candidate finite-beta sign-row unit for the scaled
bridge.  The production and replay commands use the existing order-30,
`t_order=37`, 180-bit Arb driver:

```text
python scripts/run_surface_scaled_bulk_cwin3p2_high_unit.py \
  --unit high_74_74p25 --lo 74 --hi 297/4
python scripts/run_surface_scaled_bulk_cwin3p2_high_unit.py \
  --unit high_74_74p25 --lo 74 --hi 297/4 --replay
```

The fixed contract is `CWIN=3/2`, beta domain `[74,297/4]`, and the closed
scaled `t` domain `[3/5, pi-(3/2)/beta]`, with deterministic midpoint
subdivision down to `min_dt=1/100000`.  Every terminal row must have an
outward-rounded strict upper bound below zero; production and replay must be
byte-identical and pass the generic high-order validator.

This is a **candidate unit only**.  It supplies no proof of the global beta
union, no sign-to-`H_tail` implication, and no promotion of G2 or G6.  The
box was selected because the lower-order CWIN=3/2 driver fails near
`t=3.0230279900127797`; that failure is not silently relabelled.
