# Incident — CWIN=8/5 frontier diagnostic (2026-07-23)

## Scope

This is a design-only diagnostic for the finite-beta frontier left by the
candidate scaled-bulk union.  It is not a production transcript and carries
no G2 or G6 promotion authority.

The target interval was the first unresolved piece above the current
candidate component, beginning at `beta=1629/16` and below the regular splice
at `beta=1000/9`.  The wrapper
`scripts/certify_bulk_beta_taylor_scaled_sign_rows_cwin8p5_design.py` was run
with the CWIN changed from `3/2` to `8/5`.

## Observations

1. A full design run on `[1629/16,1633/16]` with order `40`, t-order `45`,
   and Arb precision `220` did not produce a transcript within the ten-minute
   execution budget.  No output was accepted as evidence.
2. A reduced run on `[1629/16,1630/16]` with order `20`, t-order `25`, and
   precision `120` failed during adaptive covering at
   `t=2.486832249399012` with `RuntimeError: bulk failure near t=...`.
3. Narrow point probes are not a substitute for the failed cover: the scaled
   backend is subject to severe cancellation at this frontier, so isolated
   interval values cannot discharge the uniform sign-row contract.

## Verdict

`CWIN=8/5` remains a candidate design seam only.  The result neither closes
the finite-beta gap nor supplies an analytic replacement for K4/H_tail.
Any future production attempt must be preregistered with a complete
beta-union, production/replay byte equality, a tail contract, and an
independent validator before it can affect G2 or G6.

