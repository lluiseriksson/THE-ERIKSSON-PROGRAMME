# G2 post-1635/16 min-8 full-cell diagnostic — preregistration

This candidate-only experiment follows two seeded-grid failures on the same
cell and the separately validated one-row micro-rescue. It changes only the
minimum recursive t width; it is not an alteration of the mathematical claim.

Frozen inputs:

- beta domain `[1635/16,3271/32]`;
- moving t domain `[3/5,pi_up-(3/2)/(1635/16)]`, with the existing five
  rational partitions and seed step `1/64`;
- `CWIN=3/2`, beta Taylor order `30`, t Taylor order `37`, Arb precision
  `180` bits;
- recursive `MIN_DT=1/100000000` throughout this cell;
- production and independent replay must be byte-identical, with current
  dependency hashes and strict negative outward upper bounds on every row.

The only admissible result is a quarantined candidate manifest with
`promotion: NONE`. A failure or timeout is an incident. No further order,
precision, beta-width, seed-step, or domain changes are licensed by this
registration, and no result can promote G2, `(H_tail)`, or G6.
