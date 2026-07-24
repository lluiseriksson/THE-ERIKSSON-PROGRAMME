# G2 two-lane collar splice — pre-registration

**State:** `DESIGN_GATE`; no G2/G6 promotion  
**Registered:** 2026-07-24, before attempting the missing beta cell
`[1629/16,3259/32]`.

The failed CWIN=`3/2` bulk unit leaves a narrow right collar.  The existing
pair mean-value certificate is a different predicate, so it may be used only
through the following explicit two-lane contract.

For the beta cell `B=[1629/16,3259/32]`, set
`lambda_lo=3/2`, `lambda_hi=19/10`, and

```text
t = pi - lambda/beta.
```

Lane A is a trimmed scaled-bulk certificate on the fixed rectangle
`[3/5, pi-lambda_hi/beta_hi]`, with CWIN=`19/10`, exact rational beta/t rows,
production/replay equality, and the usual outward-rounded strict upper sign.
Lane B is the existing 500-bit pair mean-value certificate on the rectangle
`B x [lambda_lo,lambda_hi]`.  Its exact pair identity and positive scaling
must be cited; it is not relabelled as a row transcript.

Promotion of this cell requires all of:

1. a fresh Lane-A production transcript and independent replay under this
   contract, with its own hashes and validator;
2. independent validation of the current Lane-B transcript and dependencies;
3. an executable collar map proving that Lane A and Lane B cover the same
   beta cell with no t gap or overlap ambiguity; and
4. a manifest with explicit lane schemas and `promotion: NONE` until the
   global finite-beta union and the separate sign-to-`H_tail` relay are closed.

Failure of Lane A, a missing replay, or a domain mismatch is terminal for this
splice attempt.  It may not be repaired by fabricating CWIN headers on the
pair transcript.
