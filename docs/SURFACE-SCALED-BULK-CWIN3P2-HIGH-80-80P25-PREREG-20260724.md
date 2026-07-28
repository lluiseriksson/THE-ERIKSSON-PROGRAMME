# High-order scaled bulk unit `[80,321/4]` — preregistration

**Registered:** 2026-07-24, before production/replay

This is one candidate unit in the unresolved finite-beta bulk bridge.  It
freezes the existing high-order evaluator and does not change any theorem
gate.

Fixed contract:

```text
beta interval  [80, 321/4]
CWIN           3/2
beta_order    30
t_order       37
min_dt        1/100000
Arb precision 180 bits
t domain      [3/5, pi-(3/2)/(321/4)]
```

Production and an independent replay must have byte-identical transcripts,
strictly negative upper endpoints on an ordered exhaustive `t` partition,
and matching dependency hashes.  A failure is retained as a negative
incident.  A pass is candidate sign evidence only: it does not prove the
absolute `(H_tail)` relay, close K2/K4, promote G2/G6, or alter the
manuscript seal.
