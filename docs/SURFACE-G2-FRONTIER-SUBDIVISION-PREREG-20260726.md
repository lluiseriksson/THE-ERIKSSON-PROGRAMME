# G2 frontier beta-subdivision diagnostic (2026-07-26)

This preregisters one bounded diagnostic for the remaining finite-beta
candidate frontier.  It does **not** promote G2, `(H_tail)`, or G6.

## Frozen contract

- beta box: `[1635/16, 6541/64]`;
- scaled sign carrier: `CWIN=3/2`;
- beta/t Taylor orders: `40/45`;
- Arb precision: `220` bits;
- recursive minimum t width: `1/200000`;
- t domain: `[3/5, pi_up - (3/2)/beta_hi]`;
- production and replay must be byte-identical after excluding only the
  provenance and wall-clock lines explicitly named by the validator.

The only admissible positive outcome is a complete strict-negative t cover
with exact rational adjacency and current dependency hashes.  A timeout,
uncertified row, or any failure near the known cancellation cell is recorded
as a design incident.  Even a passing cover remains quarantined candidate
sign evidence: it does not prove the sign-to-`(H_tail)` relay and cannot alter
the manuscript or terminal gate.
