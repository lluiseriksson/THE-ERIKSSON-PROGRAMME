# Surface finite-bulk terminal promotion

**Verdict:** `FINITE_BULK_SIGN_CERTIFIED`

This record explains a deliberate role promotion of the finite scaled-sign
archive.  The historical manifests carried `promotion: NONE`: at that time
their proposed relay still depended on the unproved extraction hypothesis
`(H_tail)`.  The terminal proof does not use that relay.  It uses the exact
Wronskian identity

```text
W = 4 F_B^2 E'
```

and a common strictly positive scaling factor.  Consequently the already
certified strict scaled signs directly imply `E'<0` once Theorem A supplies
`F_B>0`.  No historical manifest was edited and no numerical output was
selected again.

## Frozen terminal contract

The auditor `scripts/audit_surface_g2_relay_admissibility.py` applies a
deterministic ownership rule to all admissible CWIN=3/2 units.  It requires:

- exact rational union `[20,1000/9]`, with no gap;
- a nonempty adjacent `t` partition in every selected unit;
- strictly negative outward-rounded upper endpoints;
- exact production/replay byte equality and manifested hashes;
- exactly 501 ownership rows;
- terminal fingerprint
  `86029ed96f88c53fd0fe18769e33577d4eee56aed553f36943dd490f09b7ae80`.

The fingerprint feeds every ownership row, the corresponding manifest
LF-normalized bytes, and both transcript LF-normalized byte strings to
SHA-256.  Changing the ownership rule or textual content of any manifest or
run therefore fails closed, while a Git-only LF/CRLF conversion does not.

## Compact G5 provenance note

The compact `[20,25]` G5 transcripts record source head
`8b4a17c0681601d0d433ed769d23ce8daa8269a9`.  The driver dependencies were
not tracked at that historical head.  The terminal validator therefore does
not claim that Git can reconstruct them from that commit.  It verifies the
dependency hashes printed in every transcript against the dependency bytes
promoted with this audit:

```text
certify_right_edge_beta_taylor_cached_extension.py 54b7f122f62d60c0a7a6f2f875708ea5be9161df1939a1db815910d62a02495b
certify_right_edge_beta_taylor_cached_design.py    205a83c5487cc936a2f91ce6551ca2f44fa78f983beb21b0d572e95b6549c9b4
certify_right_edge_beta_taylor_arb.py              d614f97a120b13b8cb02b00f6906fd76780c6c329062cdc71fec499083137cdc
certify_bulk_beta_taylor_arb.py                    f69cfaadd311218a749039a64ad4ae3a68e4bd3e0527be5ac75744955f97b9aa
```

This is a provenance limitation, not a missing numerical check: 721 beta
boxes, 721 normalized boxes, and 18,659 regular boxes are checked in both
production and replay.

## Reproduction

```powershell
python scripts/audit_surface_g2_relay_admissibility.py
python scripts/audit_surface_finite_role_relay.py
python -m pytest -q tests/test_surface_g2_relay_admissibility.py tests/test_surface_finite_role_relay.py
```

This promotion is confined to the direct finite-beta Wronskian role.  It
does not by itself promote the high-beta half-line or the final manuscript
seal.
