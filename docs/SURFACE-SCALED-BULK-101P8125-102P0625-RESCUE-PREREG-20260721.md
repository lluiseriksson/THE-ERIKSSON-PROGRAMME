# Scaled-bulk rescue preregistration: `[101.8125,102.0625]`

**Registered:** 2026-07-21, before reading the new run

This is an isolated candidate rescue for the first gap immediately after the
passing high-order unit `[101.75,101.8125]`.  The beta interval is fixed as

```text
[3258/32, 3266/32] = [101.8125,102.0625]
```

and uses the existing order-40/order-45 rescue contract:

```text
CWIN=3/2, beta_order=40, t_order=45,
Arb precision=220 bits, min_dt=1/200000.
```

Acceptance requires a complete strict-negative `t` cover, production and
independent replay byte identity, and the dedicated rescue validator.  A
green unit remains candidate evidence only: it does not promote G2/G6, does
not discharge the finite-beta derivative-tail contract, and does not prove
the sign-to-`H_tail` relay.  A failure is retained as a negative incident;
the beta interval and rescue constants may not be widened after observing
output.
