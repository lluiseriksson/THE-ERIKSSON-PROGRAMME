# K2 covariance positive-mass carrier — conditioning failure (2026-07-26)

Using pointwise-positive mass intervals avoids the `M`-contains-zero failure,
but the centered between-cell covariance remains far too wide. Production and
replay are byte-identical:

```text
production/replay SHA-256: 92382A1AB67D68FBA4EFA291575FBCAC8AC0BE0DEFB33CDB4A60DAD9E48D8984
grid 12: M_lower=0.3703526010..., covariance bound radius=5.47e6
grid 24: M_lower=0.5912724506..., covariance bound radius=2.11e2
terminal line: POSITIVE MASS COVARIANCE DESIGN ONLY; NO K2 PROMOTION
```

The exact covariance algebra is therefore validated only formally; this
midpoint/Hessian enclosure does not preserve enough correlation to meet the
R3 scale. No K2/G2/G6/manuscript state changes.
