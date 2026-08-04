# CWIN=3/2 low-beta continuation [27,28] — preregistration

**Status:** candidate-only; no G2/G6 promotion

Freeze four adjacent beta units:

```text
beta       [27,28] split into [27,109/4], [109/4,55/2], [55/2,111/4], [111/4,28]
CWIN       3/2
beta_order 30
t_order    37
min_dt     1/100000
precision  180 Arb bits
t-domain   [3/5, pi_upper - (3/2)/beta_hi]
```

Require independent production/replay, exact rational endpoints, complete
adjacent t rows, strict outward negativity, and generic validator passes.
Passing rows remain candidate evidence only; no G2/G6 or manuscript promotion
is authorized.
