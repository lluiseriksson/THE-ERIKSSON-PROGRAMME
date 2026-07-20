# Incident: CWIN=8/5 design probe timed out

Date: 2026-07-20

## Registered scope

This was a design-only probe of the proposed moving-edge cut
`CWIN=8/5`, using
`scripts/certify_bulk_beta_taylor_scaled_sign_rows_cwin8p5_design.py` with

```text
beta interval [1629/16, 3259/32]
beta order 40
t order 45
Arb precision 220 bits
```

The wrapper changes only the moving-edge cut in the isolated CWIN=3/2
backend.  It does not write a production manifest and carries no G2 or G6
theorem load.

## Result

The process was allowed to run for 600 seconds and exited with code 124 from
the command timeout.  No terminal sign-row transcript, replay, or coverage
claim was produced.  The probe is therefore **non-evidence**.

A cheaper repeat on the same beta cell, with order `24`, t-order `30`, and
160-bit precision, was also allowed 120 seconds and exited with code 124.
This rules out treating the first timeout as merely a high-order configuration
artefact; it still does not constitute a mathematical failure of the route.

## Consequence

The timeout does not show that CWIN=8/5 fails mathematically, nor that it
rescues the seam.  A future attempt must first be preregistered with a bounded
algorithmic budget (including a subdivision cap and a deterministic timeout),
then run production and independent replay.  Even a successful CWIN=8/5 sign
cover would address only domain coverage; it would not prove the separate
`H_tail` relay required by G2/G6.

The authoritative gate states are unchanged.
