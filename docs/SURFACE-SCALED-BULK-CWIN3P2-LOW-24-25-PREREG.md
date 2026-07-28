# CWIN=3/2 low-beta continuation [24,25] — preregistration

**Status:** candidate-only; no G2/G6 promotion

Freeze four adjacent beta units before reading outputs:

```text
beta       [24,25] split into [24,49/2], [49/2,97/4], [97/4,99/4], [99/4,25]
CWIN       3/2
beta_order 30
t_order    37
min_dt     1/100000
precision  180 Arb bits
t-domain   [3/5, pi_upper - (3/2)/beta_hi]
```

Production and replay must be independent, with exact rational endpoints,
complete adjacent t rows, strictly negative outward upper bounds, and generic
validator passes. A pass is candidate evidence only and does not alter G2,
the relay status, or the manuscript.
