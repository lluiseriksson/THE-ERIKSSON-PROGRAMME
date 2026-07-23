# Rescue retry timeout: `[101.8125,101.828125]`

The already pre-registered order-40/order-45 rescue was retried with the
unchanged contract (`CWIN=3/2`, 220 Arb bits, `min_dt=1/200000`).  The bounded
300-second execution ended before a production transcript was emitted.  No
sign row, coverage, or margin is inferred from this run, and no output was
admitted.

This repeats the earlier inconclusive timeout for the same subcell.  The
backend remains an execution-budget failure, not a mathematical result; G2,
G6, and the finite-beta relay are unchanged.
