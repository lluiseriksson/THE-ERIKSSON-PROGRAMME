# G2 post-1635/16 width-1/32 diagnostic — preregistration

This is a new candidate-only diagnostic following the frozen-cell failure in
`INCIDENT-G2-POST1635-SEEDED-FAIL-20260725.md`. It changes only the beta cell
width; it does not alter the Taylor orders, precision, t partition, or the
promotion rules.

Frozen parameters:

- beta domain `[1635/16,3271/32]` (width `1/32`);
- `CWIN=3/2`, beta Taylor order `30`, t Taylor order `37`;
- Arb precision `180` bits and seeded t step `1/64`;
- same moving endpoint `pi_up-(3/2)/beta_lo` and existing seeded-grid code;
- strict negative upper bounds, exact production/replay byte equality, and
  complete dependency hashes are required.

The only admissible output is a `current-candidate` manifest with
`promotion: NONE`; a failure or timeout is recorded as an incident. No
authoritative G2/G6 state or manuscript text may change from this diagnostic.

