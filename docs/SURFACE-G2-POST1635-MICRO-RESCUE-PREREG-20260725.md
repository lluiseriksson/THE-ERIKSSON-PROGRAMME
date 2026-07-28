# G2 post-1635/16 micro-rescue — preregistration

The width-`1/32` diagnostic localized its first failure to a cancellation
cell near `t=3.123099211`. A read-only point audit showed that the same frozen
beta/Taylor enclosure becomes strictly negative only after t subdivision below
`1e-7`. This preregisters one local test; it is not a global parameter change.

Frozen inputs:

- beta box `[1635/16,3271/32]`;
- t box `[3123099/1000000,31231/10000]`;
- `CWIN=3/2`, beta order `30`, t order `37`, Arb precision `180`;
- existing cached backend and exact `BetaTaylorBox` implementation;
- `MIN_DT=1/10^8` for this local diagnostic only.

Success requires every recursively generated t row to have strict negative
outward upper endpoint and production/replay byte equality. Failure or timeout
is recorded as an incident. Even success is candidate-only and cannot promote
G2, `(H_tail)`, or G6; the full beta/t cover and the analytic relay remain
separate obligations.

