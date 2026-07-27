# G2 audit correction: moving seam endpoint (2026-07-27)

The read-only relay audit originally checked the moving right seam at the
lower beta endpoint of each box.  That is unsound: the required endpoint

\[
t_{\rm seam}(\beta)=\pi-\frac{3}{2\beta}
\]

is strictly increasing in `beta`.  A positive-width box must therefore be
checked at `beta_hi`, not `beta_lo`.  The production driver already uses
`PI_UP - CWIN/hi`; only the audit predicate was wrong.  A regression test now
locks this convention (`tests/test_surface_g2_relay_admissibility.py`).

After the correction, the authoritative relay audit remains blocked and finds
the genuine beta gap `[81,86]` among the older `current` manifests.  All
twenty rescue-300 repair units through `[343/4,86]` have now passed
production/replay and the independent validator.  The exact-union audit
therefore reports no remaining rational gap.  Its separate raw-adjacency
diagnostic remains false because valid historical boxes overlap; the
correction and canonical ownership chain are recorded in
`INCIDENT-G2-AUDIT-OVERLAP-UNION-20260727.md`.  The rescue manifests remain
`current-candidate` pending the role audit.

No theorem, manifest status, or manuscript claim is promoted by this repair.
