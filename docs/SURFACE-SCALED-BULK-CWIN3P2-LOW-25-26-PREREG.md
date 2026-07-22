# CWIN=3/2 low-beta continuation [25,26] — preregistration

**Status:** candidate-only; no G2/G6 promotion

Freeze four adjacent beta units:

```text
beta       [25,26] split into [25,101/4], [101/4,51/2], [51/2,103/4], [103/4,26]
CWIN       3/2
beta_order 30
t_order    37
min_dt     1/100000
precision  180 Arb bits
t-domain   [3/5, pi_upper - (3/2)/beta_hi]
```

Independent production/replay, exact rational endpoints, complete adjacent
t rows, strict outward negativity, and the generic validator are required.
Passing rows remain candidate evidence only; no G2/G6 or manuscript promotion
is authorized.
