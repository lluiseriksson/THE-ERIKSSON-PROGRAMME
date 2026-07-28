# G2 mid-cover order-22 repair — unit 20 result

**State:** candidate evidence only; no G2/G6 promotion

The preregistered repair in
`SURFACE-G2-CWIN3P2-MID-COVER-ORDER22-REPAIR-UNIT20-PREREG-20260724.md`
was run for beta unit `20 = [213/4,107/2]` with `CWIN=3/2`, beta Taylor
order 22, `t` Taylor order 25, 180 Arb bits, and minimum `t` width
`1/100000`. The frozen domain was
`[3/5, PI_UP-(3/2)/(107/2)]`.

## Result

- Production: **PASS**, 154 adjacent `t` rows.
- Replay: **PASS**, 154 rows.
- Production and replay files are byte-identical.
- Worst outward-rounded upper bound:
  `-7.8320657323221211782350184787988110415324159024295849328938582726698527841106601e-60 +/- 3.47e-140`.
- SHA-256 (production and replay):
  `64123ff9320d94375b8f5d680d22209c805f07463d53ff42e7326cf01af62b28`.
- The transcript records the wrapper, base driver, evaluator, and prereg
  document hashes; an independent parser checked the frozen headers, exact
  domain, adjacency, strict negativity, row count, and production/replay
  byte equality.

This closes the operational order-20 timeout for this unit, but it does not
prove the absolute `(H_tail)` bound, the finite-beta relay, K2, G2, or G6.
The transcript therefore remains quarantined sign evidence until the
manifest and relay lemma are independently completed.
