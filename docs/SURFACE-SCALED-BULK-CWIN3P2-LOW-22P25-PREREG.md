# CWIN=3/2 low-beta continuation — preregistration

**Status:** candidate-only; no G2/G6 promotion

Before reading the next outputs, freeze three adjacent beta units:

```text
beta       [89/4, 23] split into [89/4,45/2], [45/2,91/4], [91/4,23]
CWIN       3/2
beta_order 30
t_order    37
min_dt     1/100000
precision  180 Arb bits
t-domain   [3/5, pi_upper - (3/2)/beta_hi]
```

Each unit must run in separate production and replay processes, preserve exact
rational endpoints, certify an adjacent t-row partition with strictly negative
outward upper bounds, and pass the generic validator with matching dependency
hashes. A failure is retained as a design incident. A pass extends only the
candidate inventory; it does not change G2, the relay status, or the manuscript.
