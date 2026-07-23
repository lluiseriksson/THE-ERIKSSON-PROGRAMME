# G2 mid-cover order-20 failures — units 09 and 29

## Observation

The current-tree regeneration of the preregistered CWIN=`3/2`, beta-order-20
mid cover was run in four disjoint segments.  Units 0–8 and 21–28 emitted
fresh passing transcripts.  Unit 09 stopped at the registered minimum
`t`-width near `t=3.0585400401294516`; unit 29 stopped near
`t=2.943900793127223`.  The driver raised its explicit
`mid-order cover failure` exception and emitted no replacement transcript for
either unit.  The high-beta segments likewise did not emit a terminal unit
before the operational run ceiling.

These are operational/conditioning failures of the frozen order-20 cover,
not counterexamples to the Wronskian sign.  The old order-22/24 files are not
reused: their headers, dependency hashes, and contracts belong to earlier
trees.

## Consequence

The 83-unit union remains incomplete and cannot enter the admissible beta
inventory.  No G2/G6 state or manuscript text is changed.

## Registered follow-up

A separate order-22 repair for precisely units 09 and 29 is registered in
`SURFACE-G2-CWIN3P2-MID-COVER-ORDER22-REPAIR-UNITS09-29-PREREG-20260723.md`.
Its production and replay must be fresh, byte-identical, and independently
validated before these units can even be labelled candidate evidence.
