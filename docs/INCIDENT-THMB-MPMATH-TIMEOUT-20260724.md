# Incident: Theorem B mpmath witness remains incomplete

**Date:** 2026-07-24  
**Scope:** `certify_thmB.py` on `beta=[1/20,3]`  
**Status:** open; no theorem or paper promotion

The Arb twin remains archived and independently reports 86 beta boxes with a
second pass at precision 170.  The canonical `mpmath.iv` transcript,
`scripts/certify_thmB_transcript.txt`, is still zero bytes.  A fresh run of

```text
python scripts/certify_thmB.py 0.05 3 100
```

was allowed 300 seconds and timed out without producing a completion
transcript.  This is recorded as an execution/provenance failure, not as a
proof of failure or success of Theorem B.  The manuscript therefore must not
describe Theorem B as having two completed interval-arithmetic witnesses until
the mpmath run finishes, its transcript is captured, and its hashes and
stability pass are audited.

The executable diagnostic is:

```text
python scripts/audit_surface_thmb_witnesses.py
```

It intentionally exits non-zero while the standard transcript is empty.  No
G2, G6, or global Surface Theorem claim is promoted by this incident record.
