# CWIN=3/2 low-beta continuation [23,24] — preregistration

**Status:** candidate-only; no G2/G6 promotion

Freeze four adjacent beta units before reading any result:

```text
beta       [23,24] split into [23,93/4], [93/4,47/2], [47/2,95/4], [95/4,24]
CWIN       3/2
beta_order 30
t_order    37
min_dt     1/100000
precision  180 Arb bits
t-domain   [3/5, pi_upper - (3/2)/beta_hi]
```

Each unit requires independent production/replay, exact rational endpoints,
an adjacent t-row partition with strictly negative outward upper bounds, and
the generic validator. A pass extends candidate evidence only. A failure is
retained as an incident; the finite relay and G2/G6 states remain unchanged.
