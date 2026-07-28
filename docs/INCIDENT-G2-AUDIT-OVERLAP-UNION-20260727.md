# G2 audit correction: redundant overlap is not a coverage gap

**Recorded:** 2026-07-27, before changing the union predicate.

After the twentieth preregistered rescue unit was generated, the read-only
relay audit reported the inconsistent pair

```text
beta_union_gaps = []
beta_union_complete = false
```

The cause was mechanical.  The audit sorted every accepted historical source
box and required consecutive boxes to be exactly adjacent.  The archive
contains redundant and partially overlapping valid boxes, so raw adjacency
fails even when the exact rational union is connected.  This is a false red,
not evidence of theorem coverage.

The corrected contract keeps the raw-adjacency diagnostic, but theorem
coverage is computed from the coalesced exact rational union.  It also emits a
deterministic canonical ownership chain.  Each ownership interval is an exact
subinterval of one accepted source certificate; the ownership intervals must
be adjacent and cover the target exactly.  A regression tests both an
innocuous overlap and a genuine rational gap.

This correction is read-only and does not promote G2 or G6.  A separate role
audit must still combine a complete finite cover with denominator positivity
and the exact direct-sign relay before any gate or manuscript state changes.
