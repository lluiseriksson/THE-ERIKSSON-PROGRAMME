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
the genuine beta gap `[81,86]` among the older `current` manifests.  The
newer rescue-300 ladder is still candidate-only and cannot silently repair
that gap.  The candidate-union audit may report a connected archive because it
includes nonterminal records; that is not an admissible G2 cover.

No theorem, manifest status, or manuscript claim is promoted by this repair.
