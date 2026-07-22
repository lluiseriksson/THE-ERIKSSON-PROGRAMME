# CWIN=3/2 low-beta continuation [26,27] — preregistration

**Status:** candidate-only; no G2/G6 promotion

Freeze four adjacent beta units:

```text
beta       [26,27] split into [26,105/4], [105/4,53/2], [53/2,107/4], [107/4,27]
CWIN       3/2
beta_order 30
t_order    37
min_dt     1/100000
precision  180 Arb bits
t-domain   [3/5, pi_upper - (3/2)/beta_hi]
```

Require independent production/replay, exact rational endpoints, complete
adjacent t rows, strict outward negativity, and validator passes. A pass is
candidate evidence only; no G2/G6 or manuscript promotion is authorized.
