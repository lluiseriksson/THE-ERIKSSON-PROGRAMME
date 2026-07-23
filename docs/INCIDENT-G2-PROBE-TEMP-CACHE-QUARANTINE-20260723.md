# G2 probe provenance quarantine

The exploratory probe pairs committed in the earlier width experiments were
generated while `certify_bulk_beta_taylor_arb.py` carried a temporary
precision-aware cache.  The authoritative backend has now been restored to
its original bytes so historical manifests remain reproducible.  The old
probe transcripts therefore retain their original files and hashes for audit
history, but are not current evidence and are deliberately excluded from the
live probe validator.

A fresh pair named
`surface_scaled_bulk_probe-current-wide-97_2-971_20[(_rerun)].txt` was
regenerated after restoration.  Its dependency hash matches the current
backend, and `scripts/validate_surface_scaled_bulk_probe_unit.py` checks that
hash explicitly.  Even this fresh pair remains exploratory and carries no
G2/G6 load.
