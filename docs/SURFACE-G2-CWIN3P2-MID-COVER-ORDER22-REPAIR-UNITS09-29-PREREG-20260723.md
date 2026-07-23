# G2 mid-cover order-22 repair for units 09 and 29

**State:** preregistered repair design; no G2/G6 promotion

This repair addresses only the two current order-20 failures recorded in
`INCIDENT-G2-MID-COVER-ORDER20-UNITS09-29-20260723.md`.

## Frozen contract

- beta units: `09 = [101/2,203/4]` and `29 = [111/2,223/4]`;
- `CWIN=3/2`, beta Taylor order `22`, `t` Taylor order `25`;
- 180 Arb bits, minimum `t` width `1/100000`;
- domain `[3/5, PI_UP-(3/2)/beta_hi]`;
- same adaptive bisection and exact rational endpoints as the order-20
  driver; no post-observation mesh changes.

## Acceptance

Each unit requires a production/replay pair with current dependency hashes,
strictly negative outward-rounded upper bounds on every adjacent `t` row,
byte-identical replay, and an independent validator that checks the exact
beta domain, contract, row adjacency, and scope footer.  A passing repair is
still quarantined sign evidence: it does not prove `(H_tail)`, close the
remaining beta gaps, or promote G2/G6.
