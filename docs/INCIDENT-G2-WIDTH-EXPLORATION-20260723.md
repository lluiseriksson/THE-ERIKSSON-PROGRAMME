# G2 beta-width exploration (2026-07-23)

The high-order CWIN=`3/2` sign-row driver was tested at wider beta panels,
without changing order, precision, or the `min_dt` stopping rule.  Two new
production/replay pairs pass the independent probe validator:

* `[97/2,971/20]` (width `1/20`), and
* `[765/16,383/8]` (width `1/16`).

Both pairs had strict-negative adjacent t rows and byte-identical replay under
the temporary cache backend.  They are now historical/quarantined because the
authoritative backend was restored; see
`INCIDENT-G2-PROBE-TEMP-CACHE-QUARANTINE-20260723.md`.

A fresh current-backend replay of `[97/2,971/20]` is retained separately and
is checked by `scripts/validate_surface_scaled_bulk_probe_unit.py`.

For comparison, the triple-width panel `[97/2,1943/40]` timed out before
emitting a transcript.  These results suggest an adaptive width schedule, but
they do not constitute a pre-registered exhaustive cover, a finite-beta union,
the sign-to-`H_tail` relay, or a G2/G6 promotion.
