# Incident: Theorem B mpmath witness timeout and repair

**Date:** 2026-07-24  
**Scope:** `certify_thmB.py` on `beta=[1/20,3]`  
**Status:** resolved by interval-underflow repair; independent re-run complete

The Arb twin remains archived and independently reports 86 beta boxes with a
second pass at precision 170.  The canonical `mpmath.iv` transcript initially
remained zero bytes.  A fresh run of

```text
python scripts/certify_thmB.py 0.05 3 100
```

was allowed 300 seconds and timed out without producing a completion
transcript.  Root cause was isolated: the stopping test converted the
positive interval endpoints to binary `float`; for order `m>=87` both the
term and the resulting `1e-60` threshold underflowed to zero, so the loop
could not terminate.  The test now compares interval endpoints directly:
`t.b < s.a*iv.mpf('1e-60')`.

After the repair, the canonical run completed with 53 adaptive boxes and a
second pass at precision 170.  Its transcript is captured with source hash
and runtime versions.  The regression
`tests/test_certify_thmB_high_order_stop.py` covers the former order-87 hang.
The earlier timeout remains part of the provenance history; it is no longer
an open evidence gap.

The executable diagnostic is:

```text
python scripts/audit_surface_thmb_witnesses.py
```

It exits zero only when both transcripts carry their completion markers.  This
closes the Theorem B two-witness documentation gap; it does not promote G2,
G6, or the global Surface Theorem by itself.
