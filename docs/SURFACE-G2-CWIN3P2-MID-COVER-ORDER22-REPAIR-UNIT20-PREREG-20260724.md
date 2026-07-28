# G2 mid-cover order-22 repair for unit 20

**State:** preregistered repair design; no G2/G6 promotion

This repair addresses the order-20 timeout documented in
`INCIDENT-G2-MID-COVER-ORDER20-UNIT19-20260723.md`.

## Frozen contract

- beta unit: `20 = [213/4,107/2]`;
- `CWIN=3/2`, beta Taylor order `22`, `t` Taylor order `25`;
- 180 Arb bits, minimum `t` width `1/100000`;
- domain `[3/5, PI_UP-(3/2)/(107/2)]`;
- same rational bisection and stopping rule as the registered order-22
  repair driver; no data-dependent mesh or endpoint changes.

## Acceptance

Production and replay must have current dependency hashes, exact beta/t
headers, adjacent `t` rows with strictly negative outward-rounded upper
bounds, and byte-identical contents.  An independent validator must check
the contract and row coverage.  Even if successful, this unit remains
quarantined sign evidence and carries no `(H_tail)`, K2, G2, or G6 load.
