# Incident: next dyadic pair mean-value cell timed out (2026-07-22)

The already registered mean-value configuration was applied without changing
orders, modes, precision, or the lambda band:

```text
beta  [13057/128,13058/128]
lambda [3/2,19/10]
modes 115, beta order 50, lambda order 50, Arb 500 bits
```

Command:

```text
python scripts/certify_surface_scaled_pair_mean_value_cell.py \
  --beta-lo 13057/128 --beta-hi 13058/128 \
  --lambda-lo 3/2 --lambda-hi 19/10 \
  --modes 115 --beta-order 50 --lambda-order 50 --precision 500
```

The bounded run reached the 120-second wall-clock limit without producing a
transcript or a verdict.  No output is admitted to the candidate cover and no
G2/G6 promotion follows.  The timeout is retained as a route-cost diagnostic;
it does not justify changing the registered orders or silently widening the
cell.
