# G2 CWIN=3/2 mid-order replacement lane

**Registered:** 2026-07-22, before production/replay  
**State:** `PREREGISTERED; NO G2 PROMOTION`

## Purpose

The high-order CWIN=`3/2` driver (beta order 30, `t` order 37) timed out on
the first current beta gap `[765/16,193/4]`.  A feasibility probe at lower
orders completed the same interval, so this document fixes a replacement
lane for one independently audited unit.  The probe is not evidence: it used
120 bits and a diagnostic minimum width.  Only the production/replay pair
under this contract may enter the candidate inventory.

## Frozen unit and evaluator

```text
beta interval: [765/16,193/4]
CWIN: 3/2
beta Taylor order: 20
t Taylor order: 25
Arb precision: 180 bits
minimum t width: 1/100000
t domain: [3/5, PI_UP - (3/2)/(193/4)]
backend: certify_bulk_beta_taylor_scaled_design.py
tail factor: 8(1+2(m+1)/beta_lo)^q
```

The scaled Bessel jets, coefficient tail, and derivative-tail majorants are
unchanged from the audited CWIN=`3/2` design.  Lowering the Taylor orders does
not weaken a sign enclosure: the retained Taylor polynomial and its outward
remainder are recomputed at the new orders.  It changes only the registered
cost/conditioning contract for this unit.

## Acceptance

The production and replay transcripts must:

1. contain the exact rational beta/t domains above;
2. partition the `t` domain into adjacent rows with strictly negative Arb
   upper endpoints;
3. use the same source head, dependency hashes, precision, orders, and
   minimum width;
4. be byte-identical after the declared LF/CRLF normalization; and
5. pass the independent coverage/hash validator.

Any timeout, nonnegative row, missing replay, or domain gap leaves this unit
non-admissible.  A passing unit remains candidate evidence only: it does not
prove the analytic implication to `(H_tail)`, close the other beta gaps, or
promote G2/G6.
