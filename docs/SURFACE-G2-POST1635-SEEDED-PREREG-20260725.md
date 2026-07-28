# G2 post-1635/16 seeded-grid cell — preregistration

This is a candidate-only diagnostic. It may not promote G2, `(H_tail)`, or
G6, and it may not alter the authoritative relay manifests.

## Frozen cell and contract

- beta domain: `[1635/16,409/4]`;
- `CWIN=3/2`, beta Taylor order `30`, t Taylor order `37`;
- Arb precision `180` bits;
- seeded t step `1/64`, with the existing moving endpoint
  `pi_up-(3/2)/beta_lo`;
- production and independent replay must be byte-identical;
- every outward-rounded sign-row upper endpoint must be strictly negative;
- the existing seeded-grid validator must accept the transcript and all
  dependency hashes must be recorded.

The only permitted result is a `current-candidate` manifest with
`promotion: NONE`. A timeout, nonnegative row, or provenance mismatch is a
falsification/incident, not a reason to change the cell, precision, order, or
seed step.
