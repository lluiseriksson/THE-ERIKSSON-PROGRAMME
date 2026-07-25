# G2 rescue preregistration: beta `[85,85.0625]`

This is a fresh, narrower rescue attempt after the order-30/37 unit
`[85,85.25]` timed out.  The frozen target is the strict scaled-Wronskian sign
on

```text
beta in [85, 1361/16],
t in [3/5, pi - (3/2)/beta],
```

using `run_surface_scaled_bulk_cwin3p2_rescue_unit.py`, the order-40/order-45,
220-bit Arb backend, with production and independent replay.  This remains
candidate-only: no `(H_tail)`, G2, G6, K2, or K4 promotion is allowed from a
single unit.  The required validator checks CWIN, frozen orders and precision,
strict negative upper bounds, complete ordered `t` coverage, and byte-identical
production/replay output.

Frozen command shape:

```text
python scripts/run_surface_scaled_bulk_cwin3p2_rescue_unit.py \
  --unit 85_85p0625_rescue --lo 85 --hi 1361/16
```

