# CWIN=3/2 rescue preregistration: `[102, 102+1/16]`

**Registered:** 2026-07-24, before reading the run output

This is one fixed candidate unit for the remaining finite-beta frontier.  The
endpoints are exact rationals:

```text
[102, 1633/16] = [102, 102.0625].
```

The contract is frozen to the already used rescue-300 backend:

```text
CWIN=3/2, beta_order=40, t_order=50,
Arb precision=300 bits, min_dt=1/100000.
```

The right seam is `t = pi - (3/2)/beta`; the driver must cover the exact
domain `[3/5, pi - (3/2)/hi]` by adjacent rational `t` boxes, each with a
strictly negative Arb upper bound.  Production and independent replay must be
byte-identical and pass the dedicated rescue validator.  A green unit remains
candidate evidence only: it does not promote G2 or G6, discharge `(H_tail)`,
or prove the sign-to-tail relay.  The interval and constants may not be
widened after observing output.  A failure is retained as a negative incident.
